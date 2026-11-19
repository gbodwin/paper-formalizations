import DirectedFlowCutGap.PhysicalBinaryEdgeFamily

/-! Bound the observed counts on reached adaptive price rows. A selected
edge grows its stored price by at most one fixed increment's field width. -/

namespace DirectedFlowCutGap.PhysicalBinaryEdgeFamilyCost

open BinaryArithmetic Polynomial RawNonnegativeRational
open RandomizedEdgeFamily BinaryEdgeFamilyArithmetic BinaryEdgeFamilyState
open PhysicalBinaryEdgeFamily
open PhysicalIntegerRoundingCost (eval_mono)
open IntegralNetworkFlow.Tabulated

noncomputable def stepCap (edge : Polynomial ℕ) (n B conf : ℕ) : ℕ :=
  edge.eval (n+n*n+queryWidth n B+1+conf)+queryBudget n B+checkBudget n (queryWidth n B)+advanceBudget n B B+12

attribute [local irreducible] PhysicalSourceReadback.run PhysicalAmplifiedBinaryEdge.run

private theorem step_width {n B C : ℕ} (D : Input n) (p : Preparation n) (demands : List (Edge n))
    (s : State n) (prices : Fits s.prices B) (gain : Fits p.gain C) (tape : Bits)
    {r : Result n} (ran : step D p demands s tape=some r) :
    ∀ a ∈ r.history, Fits a.prices (B+C) := by
  let q := query D p demands s
  have mapped : ((PhysicalAmplifiedBinaryEdge.run D.confidence q.input (PhysicalEdgeFamily.runnerMode D.strategy) tape).map
      (finishStep p s q))=some r := ran
  obtain ⟨round,_,rfl⟩ := Option.map_eq_some_iff.mp mapped
  intro out mem
  change out ∈ ((check q round.output).1.map (advance p s)).map Prod.fst at mem
  cases tag : (check q round.output).1 with
  | none => simp [tag] at mem
  | some mask =>
    simp only [tag,Option.map_some,Option.mem_some_iff] at mem
    rw [← mem]
    exact (advance_fits_paid p s mask prices gain).1

set_option maxHeartbeats 1300000 in
private theorem step_paid {n B : ℕ} (edge : Polynomial ℕ)
    (edgeBound : ∀ {n B : ℕ} (κ : ℕ) (D : EncodedEdgeLineInput.Input n)
      (mode : ChargedVertexModes.Mode) (tape : Bits), 1 ≤ B →
      (∀ u v : Fin n, D.costs[u.val][v.val].num.size ≤ B ∧ D.costs[u.val][v.val].den.size ≤ B) →
      ∀ {out : PhysicalAmplifiedEdgeSolver.EdgeResult n}, PhysicalAmplifiedBinaryEdge.run κ D mode tape=some out →
        out.dispatch+out.readback+out.roundingAndSelection ≤ edge.eval (n+D.demands.length+B+κ))
    (D : Input n) (p : Preparation n) (demands : List (Edge n)) (hd : demands.length ≤ n*n)
    (s : State n) (w : Fits p.adjusted B) (a : p.factor.Bounded B) (prices : Fits s.prices B) (g : Fits p.gain B)
    (tape : Bits) {r : Result n} (ran : step D p demands s tape=some r) :
    r.total ≤ stepCap edge n B D.confidence := by
  let q := query D p demands s
  let W := queryWidth n B
  change (PhysicalAmplifiedBinaryEdge.run D.confidence q.input (PhysicalEdgeFamily.runnerMode D.strategy) tape).map (finishStep p s q)=some r at ran
  obtain ⟨round,called,rfl⟩ := Option.map_eq_some_iff.mp ran
  obtain ⟨b,pre⟩ : QueryFits q W ∧ q.paid ≤ queryBudget n B := query_fits_paid D p demands s w a prices
  have widths (u v : Fin n) := Code.bounded_bits (b.prices u v)
  have edgePaid := edgeBound D.confidence q.input (PhysicalEdgeFamily.runnerMode D.strategy) tape (Nat.le_add_left 1 W) widths called
  have hsize : n+q.input.demands.length+(W+1)+D.confidence ≤ n+n*n+W+1+D.confidence := by
    change n+demands.length+(W+1)+D.confidence ≤ _
    omega
  have work := edgePaid.trans (eval_mono edge hsize)
  let c := check q round.output
  have checked : c.2 ≤ checkBudget n W := check_paid q b round.output
  have updated : ((c.1.map (advance p s)).map Prod.snd).getD 0 ≤ advanceBudget n B B := by
    cases mask : c.1 with
    | none => simp only [Option.map_none,Option.getD_none,Nat.zero_le]
    | some m =>
      simp only [Option.map_some,Option.getD_some]
      exact (advance_fits_paid p s m prices g).2
  change round.dispatch+round.readback+round.roundingAndSelection+
    (q.paid+c.2+((c.1.map (advance p s)).map Prod.snd).getD 0+12) ≤
    edge.eval (n+n*n+W+1+D.confidence)+queryBudget n B+checkBudget n W+advanceBudget n B B+12
  omega

private theorem stages_paid {n C cap per : ℕ} (one : State n → Bits → Option (Result n))
    (stepFits : ∀ s B, Fits s.prices B → ∀ tape r, one s tape=some r → ∀ a ∈ r.history, Fits a.prices (B+C))
    (stepBound : ∀ s, Fits s.prices cap → ∀ tape r, one s tape=some r → r.total ≤ per)
    (k : ℕ) (start : Option (State n)) (tape : Bits)
    (admitted : ∀ s ∈ start, ∃ B, Fits s.prices B ∧ B+k*C ≤ cap)
    {r : Result n} (ran : stages one k start tape=some r) : r.total ≤ k*per := by
  induction k generalizing start tape r with
  | zero =>
    simp only [stages,Option.some.injEq] at ran
    rw [← ran]
    simp [Result.total]
  | succ k ih =>
    cases start with
    | none =>
      simp only [stages,Option.some.injEq] at ran
      rw [← ran]
      exact Nat.zero_le _
    | some s =>
      obtain ⟨B,fit,allowed⟩ := admitted s (by simp)
      change (B+(k+1)*C ≤ cap) at allowed
      change ((one s tape).bind fun first =>
        (stages one k first.history first.suffix).map first.add)=some r at ran
      cases first : one s tape with
      | none => simp [first] at ran
      | some out =>
        cases later : stages one k out.history out.suffix with
        | none => simp [first,later] at ran
        | some done =>
          have space : B+C+k*C ≤ cap := by rw [Nat.add_mul,Nat.one_mul] at allowed; omega
          have base : B ≤ cap := by omega
          have firstPaid := stepBound s (fit.mono base) tape out first
          have tailPaid := ih out.history out.suffix (fun a mem =>
            ⟨B+C,stepFits s B fit tape out first a mem,space⟩) later
          simp only [first,later,Option.bind_some,Option.map_some,Option.some.injEq] at ran
          rw [← ran]
          change _ ≤ (k+1)*per
          rw [Nat.add_mul,Nat.one_mul]
          unfold Result.total Result.add at *
          dsimp only
          omega

def gainWidth {R : Type*} [Semiring R] (n B : R) : R := 3*setupWidth n B+1

def horizonBound {R : Type*} [Semiring R] (n B : R) : R := 2*n*(2*n+n*n*(B+1)+3)+1

def priceBound {R : Type*} [Semiring R] (n B : R) : R :=
  B+1+horizonBound n B*gainWidth n B

noncomputable def runCap (edge : Polynomial ℕ) (n B conf : ℕ) : ℕ :=
  prepareBudget n B+BinaryEdgeFamilyControls.budget n (n*n*(B+1))+
    ChargedEdgeThresholdDemands.demandBudget n B+8*horizonBound n B+
      horizonBound n B*stepCap edge n (priceBound n B) conf+12

set_option maxHeartbeats 1600000 in
theorem run_paid : ∃ edge : Polynomial ℕ, ∀ {n B : ℕ} (D : Input n) (_fit : InputFits D B) (tape : Bits)
    {r : Result n}, run D tape=some r → r.total ≤ runCap edge n B D.confidence := by
  obtain ⟨q,hq⟩ := PhysicalBinaryEdgeCost.edge_polynomial
  refine ⟨q,?_⟩
  intro n B D fit tape r actual
  let p := prepare D
  let ctrl := BinaryEdgeFamilyControls.compute n p.1.total
  let table := ChargedEdgeThresholdDemands.demands D.adjacency D.weights
  let T := horizonBound n B
  let C := gainWidth n B
  let W := priceBound n B
  let per := stepCap q n W D.confidence
  obtain ⟨weights,gain,totalWidth,prepPaid⟩ := prepare_fits_paid D fit.2 fit.1
  have countPaid : ctrl.paid ≤ BinaryEdgeFamilyControls.budget n (n*n*(B+1)) :=
    BinaryEdgeFamilyControls.compute_paid p.1.total totalWidth
  have counted : ctrl.horizon=rounds D := by
    simp only [ctrl,BinaryEdgeFamilyControls.compute_horizon,p,prepare_total,rounds]
  have Tlimit : ctrl.horizon ≤ T := counted.trans_le (rounds_le D fit)
  change runPrepared D p ctrl tape=some r at actual
  change r.total ≤ prepareBudget n B+BinaryEdgeFamilyControls.budget n (n*n*(B+1))+
    ChargedEdgeThresholdDemands.demandBudget n B+8*T+T*per+12
  by_cases small : ctrl.small=true
  · simp only [runPrepared,ite_eq_left small,Option.some.injEq] at actual
    rw [← actual]
    simp only [Result.total,Nat.zero_add]
    change p.2 ≤ _ at prepPaid
    omega
  · simp only [runPrepared,ite_eq_right small] at actual
    let one := step D p.1 table.1
    change (stages one ctrl.horizon (some (initial n)) tape).map
      (fun r => { r with arithmetic := p.2+ctrl.paid+table.2+r.arithmetic+12 })=some r at actual
    obtain ⟨base,ran,rfl⟩ := Option.map_eq_some_iff.mp actual
    have hB : B+1 ≤ W := Nat.le_add_right _ _
    have hC : C ≤ W := by
      have one : 1 ≤ T := Nat.le_add_left _ _
      have many : C ≤ T*C := by simpa only [Nat.one_mul] using Nat.mul_le_mul_right C one
      exact many.trans (Nat.le_add_left _ _)
    have dims : table.1.length ≤ n*n := by
      unfold table
      rw [ChargedEdgeThresholdDemands.demands_value]
      unfold RationalEdgeThresholds.demands
      apply (List.length_filter_le ..).trans
      simp [List.length_flatMap]
    have factor : p.1.factor.Bounded B := fit.1
    have guard : ∀ state ∈ some (initial n), ∃ b, Fits state.prices b ∧ b+ctrl.horizon*C ≤ W := by
      intro state g
      have eq := Option.mem_some_iff.mp g
      rw [← eq]
      exact ⟨B+1,initial_fit n _,Nat.add_le_add_left (Nat.mul_le_mul_right _ Tlimit) _⟩
    have actualStage : base.total ≤ ctrl.horizon*per :=
      stages_paid one (C:=C) (cap:=W) (per:=per)
        (fun s b valid bits r call => step_width D p.1 table.1 s valid gain bits call)
        (fun s valid bits r call => step_paid q hq D p.1 table.1 dims s (weights.mono hB)
          (Code.bounded_mono factor (Nat.le_trans (Nat.le_succ _) hB)) valid (gain.mono hC) bits call)
        ctrl.horizon (some (initial n)) tape guard ran
    have all := actualStage.trans (Nat.mul_le_mul_right _ Tlimit)
    have dp : table.2 ≤ ChargedEdgeThresholdDemands.demandBudget n B := ChargedEdgeThresholdDemands.demands_paid _ _ fit.2
    change p.2 ≤ _ at prepPaid
    unfold Result.total at all
    change base.dispatch+base.readback+base.roundingAndSelection+(p.2+ctrl.paid+table.2+base.arithmetic+12) ≤
      prepareBudget n B+BinaryEdgeFamilyControls.budget n (n*n*(B+1))+
        ChargedEdgeThresholdDemands.demandBudget n B+8*T+T*per+12
    omega

noncomputable def thresholdPolynomial (n B : Polynomial ℕ) : Polynomial ℕ :=
  let width := n*(B+2)+1
  let relax := 2+4096*(width+B+3)^2+64
  let pass := n*((n+1)*relax+17)+1
  let rounds := n*(pass+6)+8
  let minimize := rounds+(n+1)*(2048*(n*(B+2)+2)^2+12)+8*n+9
  let visit := n*((8*n+27)+32)+32
  let search := n*(n*(visit+4)+5)+25*n+37
  let sum := n*(2048*((n+1)*(B+1)+1)^2+4)+1
  let recover := search+n*(2+6)+sum+9
  let route := minimize+recover+6
  n*n*(route+2048*(n*(B+1)+2)^2+4+6)+1+12*n*n+10*n+5

theorem thresholdPolynomial_eval (n B : Polynomial ℕ) (x : ℕ) :
    (thresholdPolynomial n B).eval x=ChargedEdgeThresholdDemands.demandBudget (n.eval x) (B.eval x) := by
  simp only [thresholdPolynomial,ChargedEdgeThresholdDemands.demandBudget,ChargedEdgeThresholdDemands.pairBudget,
    BinaryFractionalWalkBounds.shortestBound,BinaryFractionalWalkBounds.minimizeBound,
    BinaryFractionalWalkBounds.roundsBound,BinaryFractionalWalkBounds.passBound,BinaryFractionalWalkBounds.relaxBound,
    BinaryFractionalWalkBounds.recoverBound,RetainedPathSearch.searchBound,RetainedPathSearch.visitBound,
    BinaryFractionalRows.sumBound,eval_add,eval_mul,eval_pow,eval_ofNat,eval_one]

noncomputable def stepPolynomial (edge n B conf : Polynomial ℕ) : Polynomial ℕ :=
  edge.comp (n+n*n+queryWidth n B+1+conf)+queryBudget n B+checkBudget n (queryWidth n B)+advanceBudget n B B+12

theorem stepPolynomial_eval (edge n B conf : Polynomial ℕ) (x : ℕ) :
    (stepPolynomial edge n B conf).eval x=stepCap edge (n.eval x) (B.eval x) (conf.eval x) := by
  simp only [stepPolynomial,stepCap,queryWidth,queryBudget,checkBudget,advanceBudget,sumBudget,
    BinaryRawRational.budget,BinaryRationalNormalize.budget,BinaryRationalNormalize.budgetBits,
    BinaryEuclidean.stepBudget,BinaryVertexReductionArithmetic.aggregateWidth,
    eval_add,eval_mul,eval_pow,eval_ofNat,eval_one,eval_comp]

noncomputable def familyPolynomial (edge : Polynomial ℕ) : Polynomial ℕ :=
  let T := horizonBound (X : Polynomial ℕ) X
  prepareBudget X X+BinaryEdgeFamilyControls.budget X (X*X*(X+1))+
    thresholdPolynomial X X+8*T+T*stepPolynomial edge X (priceBound X X) X+12

theorem familyPolynomial_eval (edge : Polynomial ℕ) (x : ℕ) :
    (familyPolynomial edge).eval x=runCap edge x x x := by
  simp only [familyPolynomial,runCap,stepPolynomial_eval,thresholdPolynomial_eval,priceBound,horizonBound,
    gainWidth,setupWidth,prepareBudget,BinaryEdgeFamilyControls.budget,sumBudget,
    BinaryRawRational.budget,BinaryVertexReductionArithmetic.aggregateWidth,
    eval_add,eval_mul,eval_pow,eval_ofNat,eval_one,eval_X]

private theorem stepCap_mono (edge : Polynomial ℕ) {n m b B c C : ℕ} (hn : n ≤ m) (hb : b ≤ B) (hc : c ≤ C) :
    stepCap edge n b c ≤ stepCap edge m B C := by
  have h : n+n*n+queryWidth n b+1+c ≤ m+m*m+queryWidth m B+1+C := by unfold queryWidth; gcongr
  have cEdge := eval_mono edge h
  unfold stepCap queryBudget checkBudget advanceBudget queryWidth sumBudget BinaryRawRational.budget
    BinaryRationalNormalize.budget BinaryRationalNormalize.budgetBits BinaryEuclidean.stepBudget
    BinaryVertexReductionArithmetic.aggregateWidth
  dsimp only
  gcongr
  exact cEdge

private theorem runCap_mono (edge : Polynomial ℕ) {n m b B c C : ℕ} (hn : n ≤ m) (hb : b ≤ B) (hc : c ≤ C) :
    runCap edge n b c ≤ runCap edge m B C := by
  have limits : horizonBound n b ≤ horizonBound m B := by unfold horizonBound; gcongr
  have price : priceBound n b ≤ priceBound m B := by unfold priceBound gainWidth setupWidth; gcongr
  have stage := stepCap_mono edge hn price hc
  unfold runCap prepareBudget BinaryEdgeFamilyControls.budget ChargedEdgeThresholdDemands.demandBudget
    ChargedEdgeThresholdDemands.pairBudget BinaryFractionalWalkBounds.shortestBound
    BinaryFractionalWalkBounds.minimizeBound BinaryFractionalWalkBounds.roundsBound BinaryFractionalWalkBounds.passBound
    BinaryFractionalWalkBounds.relaxBound BinaryFractionalWalkBounds.recoverBound
    RetainedPathSearch.searchBound RetainedPathSearch.visitBound BinaryFractionalRows.sumBound
    sumBudget setupWidth BinaryRawRational.budget BinaryVertexReductionArithmetic.aggregateWidth
  dsimp only
  gcongr

theorem family_polynomial : ∃ p : Polynomial ℕ, ∀ {n B : ℕ} (D : Input n) (_fit : InputFits D B) (tape : Bits)
    {r : Result n}, run D tape=some r → r.total ≤ p.eval (n+B+D.confidence) := by
  obtain ⟨q,hq⟩ := run_paid
  refine ⟨familyPolynomial q,?_⟩
  intro n B D fit tape r ran
  rw [familyPolynomial_eval]
  exact (hq D fit tape ran).trans (runCap_mono q (by omega) (by omega) (by omega))

theorem calibrated_polynomial {k : ℕ} (positive : 0<k) (M : ℕ) :
    ∃ p : Polynomial ℕ, ∀ {n B : ℕ} (κ : ℕ) (adj : BinaryFractionalWalkOracle.Adjacency n)
      (w : RationalEdgeThresholds.Weights n) (_fit : AdaptiveWidthEnvelope.StoredWeights w B)
      (tape : Bits) {r : Result n}, run (calibratedParameters k M κ adj w) tape=some r →
        r.total ≤ p.eval (n+B+κ) := by
  obtain ⟨q,hq⟩ := family_polynomial
  let width : Polynomial ℕ := X+C M.size+X+X*X*(X+1)+3
  let conf := X+horizonBound X width
  let pad := X+width+conf
  refine ⟨q.comp pad,?_⟩
  intro n B κ adj w fit tape r ran
  let D := calibratedParameters k M κ adj w
  let x := n+B+κ
  have ny : n ≤ x := by unfold x; omega
  have By : B ≤ x := by unfold x; omega
  have ky : κ ≤ x := by unfold x; omega
  have kw : AdaptiveWidthEnvelope.width n B M ≤ width.eval x := by
    simp only [width,AdaptiveWidthEnvelope.width,eval_add,eval_C,eval_mul,eval_one,eval_ofNat,eval_X]
    have s : M.size+n+n*n*(B+1)+3 ≤ M.size+x+x*x*(x+1)+3 := by gcongr
    exact max_le (by omega) (by omega)
  have kc : D.confidence ≤ conf.eval x := by
    have actual := AdaptiveWidthEnvelope.calibrated_confidence positive M κ adj w fit
    change D.confidence ≤ κ+horizonBound n (AdaptiveWidthEnvelope.width n B M) at actual
    apply actual.trans
    simp only [conf,horizonBound,eval_add,eval_mul,eval_ofNat,eval_one,eval_X]
    gcongr
  have sized : n+AdaptiveWidthEnvelope.width n B M+D.confidence ≤ pad.eval x := by
    simp only [pad,eval_add,eval_X]
    omega
  rw [eval_comp]
  exact (hq D (AdaptiveWidthEnvelope.calibrated_fits positive M κ adj w fit) tape ran).trans (eval_mono q sized)

end DirectedFlowCutGap.PhysicalBinaryEdgeFamilyCost
