import DirectedFlowCutGap.PairedCutSearch
import DirectedFlowCutGap.PhysicalBinaryEdgeWire

/-! The competing edge solvers use the same literal fair tape and the
original edge objective. Retained line costs are used only to score cuts. -/
namespace DirectedFlowCutGap.PhysicalPairedEdge

open scoped NNReal
open BinaryArithmetic BinaryRational FiniteDrawTrees FiniteAmplification Polynomial
open EncodedEdgeLineInput PhysicalAmplifiedBinaryEdge
open PhysicalAmplifiedEdgeSolver (EdgeResult model)
open PairedCutSearch (Result)
open PhysicalIntegerRoundingCost (eval_mono)

private def one {n : ℕ} (κ : ℕ) (mode : ChargedVertexModes.Mode) (D : Input n) (bits : Bits) :
    Option (Result (EncodedEdgeSolver.Output n)) :=
  (PhysicalAmplifiedBinaryEdge.run κ D mode bits).map fun r =>
    ⟨r.output,r.suffix,r.dispatch+r.readback+r.roundingAndSelection⟩

private theorem one_observe {n : ℕ} (κ : ℕ) (mode : ChargedVertexModes.Mode) (D : Input n) (bits : Bits) :
    (one κ mode D bits).map Result.observe=
      PairedCutSearch.observeTape (EncodedEdgeSolver.bitTree κ D (model mode)) bits := by
  unfold one
  rw [Option.map_map]
  exact PhysicalAmplifiedBinaryEdge.run_observe κ D mode bits

private def lineOutput {n : ℕ} : EncodedEdgeSolver.Output n → EncodedVertexSolver.Output (lineSize n) × ℕ
  | .cut mask =>
    let line := BinaryEdgeProjection.toLine mask
    (.cut line.1,line.2+2)
  | .infeasible _ | .invalid => (.invalid,2)

private theorem lineOutput_paid {n : ℕ} (a : EncodedEdgeSolver.Output n) :
    (lineOutput a).2 ≤ BinaryEdgeProjection.lineMaskBudget n+2 := by
  cases a with
  | cut mask => exact Nat.add_le_add_right (BinaryEdgeProjection.toLine_paid mask) 2
  | infeasible _ | invalid => exact Nat.le_add_left _ _

private def score {n : ℕ} (c : BinaryFractionalRows.Row (lineSize n)) (a : EncodedEdgeSolver.Output n) : Fraction × ℕ :=
  let output := lineOutput a
  let measured := BinaryCutPriceSelection.cutScore c output.1
  (measured.1,measured.2+output.2)

private theorem score_price {n : ℕ} (D : Input n) (a : EncodedEdgeSolver.Output n) :
    ((decode (score (lineWithCost D).1.costs a).1).realValue : ℝ)=EncodedEdgeSolver.outputPrice D a := by
  change ((decode (BinaryCutPriceSelection.cutScore (lineWithCost D).1.costs (lineOutput a).1).1).realValue : ℝ)=_
  rw [BinaryCutPriceSelection.cutScore_decodes,EncodedVertexAmplification.codePrice_value,line_value,
    PhysicalEdgeSolver.decode_binaryLineInput]
  cases a with
  | cut mask =>
    simp only [lineOutput,BinaryEdgeProjection.toLine_value]
    exact congrArg (fun x : ℝ≥0 => (x : ℝ)) (toLine_cost D mask)
  | infeasible _ | invalid =>
    simp [lineOutput,EncodedVertexSolver.outputPrice,EncodedVertexSolver.outputMask,EncodedCutSelection.optionPrice,
      EncodedEdgeSolver.outputPrice,EncodedEdgeSolver.outputEdges,edgeCutCost]

def run {n : ℕ} (κ : ℕ) (D : Input n) (bits : Bits) : Option (Result (EncodedEdgeSolver.Output n)) :=
  let line := lineWithCost D
  (PairedCutSearch.run (score line.1.costs) (one κ .mass D) (one κ .size D) bits).map
    (fun r => { r with paid := r.paid+line.2 })

def tree {n : ℕ} (κ : ℕ) (D : Input n) : FiniteDrawTrees.Tree (EncodedEdgeSolver.Output n) :=
  PairedCutSearch.tree (score (lineWithCost D).1.costs)
    (EncodedEdgeSolver.bitTree κ D EncodedEdgeSolver.massMode)
    (EncodedEdgeSolver.bitTree κ D EncodedEdgeSolver.sizeMode)

def tapeBudget {n : ℕ} (κ : ℕ) (D : Input n) : ℕ := 2*EncodedSolverBits.edgeBudget κ D

theorem run_observe {n : ℕ} (κ : ℕ) (D : Input n) (bits : Bits) :
    (run κ D bits).map Result.observe=PairedCutSearch.observeTape (tree κ D) bits := by
  unfold run
  rw [Option.map_map]
  exact PairedCutSearch.run_observe _ _ _ _ _ (one_observe κ .mass D) (one_observe κ .size D) bits

theorem tree_within {n : ℕ} (κ : ℕ) (D : Input n) : Within (tapeBudget κ D) (tree κ D) := by
  simpa only [tree,tapeBudget,two_mul] using
    PairedCutSearch.tree_within (EncodedSolverBits.edge_mass_within κ D)
      (EncodedSolverBits.edge_size_within κ D) (score (lineWithCost D).1.costs)

theorem tree_binary {n : ℕ} (κ : ℕ) (D : Input n) : LazyFairBitTrees.Binary (tree κ D) :=
  PairedCutSearch.tree_binary (EncodedEdgeSolver.bitTree_binary ..) (EncodedEdgeSolver.bitTree_binary ..) _

theorem support_valid {n : ℕ} (κ : ℕ) (D : Input n) {out : EncodedEdgeSolver.Output n}
    (h : out ∈ (ideal (tree κ D)).support) : EncodedEdgeSolver.Valid D out := by
  rcases PairedCutSearch.support _ _ _ h with hm | hs
  · exact EncodedEdgeSolver.mass_support_valid _ _ hm
  · exact EncodedEdgeSolver.size_support_valid _ _ hs

theorem fairTape {n : ℕ} (κ : ℕ) (D : Input n) :
    (EncodedSolverBits.fairTape (tapeBudget κ D)).map (fun bits => (run κ D bits).map Result.output) =
      (ideal (tree κ D)).map some :=
  PairedCutSearch.fairTape (run κ D) (tree κ D) (run_observe κ D) (tree_within κ D) (tree_binary κ D)

def runOn {n : ℕ} (κ : ℕ) (D : EncodedEdgeInput.Input n) (tape : Bits) :
    Option (Result (EncodedEdgeSolver.Output n)) :=
  let x := PhysicalBinaryEdgeWire.decodeWithCost D
  (run κ x.1 tape).map (fun r => { r with paid := r.paid+x.2 })

theorem runOn_observe {n : ℕ} (κ : ℕ) (D : EncodedEdgeInput.Input n) (tape : Bits) :
    (runOn κ D tape).map Result.observe=
      PairedCutSearch.observeTape (tree κ (EncodedEdgeInput.decodeInput D)) tape := by
  unfold runOn
  simp only [PhysicalBinaryEdgeWire.decode_value,Option.map_map]
  exact run_observe κ (EncodedEdgeInput.decodeInput D) tape

def withCost (κ : ℕ) (source tape : Bits) :
    PhysicalCoverAccess.Read (Σ n,Result (EncodedEdgeSolver.Output n)) :=
  let parsed := ChargedSourceAssembly.edge source
  (PhysicalVertexSolver.prepareOn (fun _ input => runOn κ input tape) parsed.1,parsed.2)

theorem complete {n : ℕ} (κ : ℕ) (D : EncodedEdgeInput.Input n) (source tape : Bits)
    (parsed : EncodedEdgeInput.parse source=some ⟨n,D⟩)
    (enough : tapeBudget κ (EncodedEdgeInput.decodeInput D) ≤ tape.length) :
    ∃ r used, (withCost κ source tape).1=some ⟨n,r⟩ ∧ r.suffix=tape.drop used ∧
      used≤tapeBudget κ (EncodedEdgeInput.decodeInput D) ∧
        EncodedEdgeSolver.Valid (EncodedEdgeInput.decodeInput D) r.output := by
  let G := EncodedEdgeInput.decodeInput D
  obtain ⟨r,k,ok,tail,length,valid⟩ := PairedCutSearch.complete (runOn κ D) (tree κ G)
    (runOn_observe κ D) (tree_within κ G) (tree_binary κ G) (fun _ => support_valid κ G) tape enough
  refine ⟨r,k,?_,tail,length,valid⟩
  simp only [withCost,ChargedSourceAssembly.edge_value]
  exact PhysicalVertexSolver.prepareOn_eq (fun _ input => runOn κ input tape) parsed ok

private theorem mode_failure {n : ℕ} (κ : ℕ) (D : Input n) (mode : EncodedEdgeSolver.Mode)
    (within : ∀ m (I : EncodedUnitCostReplication.Input m),
      Within (EncodedUniformRounding.drawBound (4*m^2)) (mode m I))
    (B : ℝ) (hB : 0 ≤ B) (bound : EncodedEdgeSolver.expectedPrice D mode ≤ B) :
    probability (ideal (EncodedEdgeSolver.bitTree κ D mode)) (fun out => 2*B < EncodedEdgeSolver.outputPrice D out) ≤
      ((max 1 n : ℕ) : ℝ) ^ (-(κ : ℝ)) := by
  rcases hB.eq_or_lt with eq | pos
  · subst B
    rw [mul_zero,PairedCutSearch.probability_gt_zero_eq_zero]
    · positivity
    · exact fun _ h => EncodedEdgeSolver.zero_price_on_support κ D mode bound h
  · exact EncodedEdgeSolver.polynomial_failure_le κ D mode within B pos bound

theorem failure_min {n : ℕ} (κ : ℕ) (D : Input n) (mass size : ℝ)
    (hm : 0 ≤ mass) (hs : 0 ≤ size)
    (em : EncodedEdgeSolver.expectedPrice D EncodedEdgeSolver.massMode ≤ mass)
    (es : EncodedEdgeSolver.expectedPrice D EncodedEdgeSolver.sizeMode ≤ size) :
    probability (ideal (tree κ D)) (fun out => min (2*mass) (2*size) < EncodedEdgeSolver.outputPrice D out) ≤
      ((max 1 n : ℕ) : ℝ) ^ (-(κ : ℝ)) :=
  PairedCutSearch.failure_min _ _ _ _ (score_price D)
    (mode_failure κ D _ (fun _ I => EncodedWeightedRounding.tree_within I) mass hm em)
    (mode_failure κ D _ (fun _ I => EncodedSizeRounding.tree_within I) size hs es)

theorem approximation_uniform :
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
      ∀ (n κ : ℕ) (D : Input n) (w : EncodedEdgeGadget.Pair n → ℝ≥0),
        IsFractionalEdgeCut D.graph w {d | d ∈ D.demands} →
        probability (ideal (tree κ D)) (fun a =>
          C*min ((n : ℝ)^ε*(totalEdgeWeight D.graph w : ℝ)^(1/2 : ℝ)) ((n : ℝ)^(1/3+ε))*
            (weightedEdgeCost D.graph D.cost w : ℝ) <
              EncodedEdgeSolver.outputPrice D a) ≤ ((max 1 n : ℕ) : ℝ)^(-(κ : ℝ)) := by
  intro ε hε
  obtain ⟨M,hM,mass⟩ := EncodedEdgeSolver.mass_expected_uniform ε hε
  obtain ⟨S,_hS,size⟩ := EncodedEdgeSolver.size_expected_uniform ε hε
  let C := max M S
  have pos : 0 < C := hM.trans_le (le_max_left _ _)
  refine ⟨2*C,by positivity,?_⟩
  intro n κ D w valid
  let m := (n : ℝ)^ε*(totalEdgeWeight D.graph w : ℝ)^(1/2 : ℝ)
  let s := (n : ℝ)^(1/3+ε)
  let q := (weightedEdgeCost D.graph D.cost w : ℝ)
  have em : EncodedEdgeSolver.expectedPrice D EncodedEdgeSolver.massMode ≤ C*m*q := by
    apply (mass n D w valid).trans
    change M*(n : ℝ)^ε*(totalEdgeWeight D.graph w : ℝ)^(1/2 : ℝ)*q ≤ _
    rw [mul_assoc M]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)) (by positivity)
  have es : EncodedEdgeSolver.expectedPrice D EncodedEdgeSolver.sizeMode ≤ C*s*q :=
    (size n D w valid).trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_right _ _)
      (by positivity)) (by positivity))
  have result := failure_min κ D (C*m*q) (C*s*q) (by positivity) (by positivity) em es
  rw [PairedCutSearch.scaled_min pos.le (by positivity : 0 ≤ q)] at result
  exact result

private theorem selection_fields {n B : ℕ} (D : Input n) (positive : 1 ≤ B)
    (fits : ∀ u v : Fin n, D.costs[u.val][v.val].num.size ≤ B ∧ D.costs[u.val][v.val].den.size ≤ B)
    (a : EncodedEdgeSolver.Output n) :
    StoredBounded (score (lineWithCost D).1.costs a).1 (lineSize n*(B+1)+1) ∧
      (score (lineWithCost D).1.costs a).2 ≤
        BinaryFractionalRows.sumBound (lineSize n) B+(BinaryEdgeProjection.lineMaskBudget n+2) := by
  have stored (i : Fin (lineSize n)) :
      StoredBounded (BinaryFractionalRows.get (lineWithCost D).1.costs i) B := by
    rw [line_value]
    simp only [PhysicalEdgeSolver.binaryLineInput,BinaryFractionalRows.get,Vector.getElem_map]
    let q := (lineInput D).costs[i.val]
    change q.num.bits.length ≤ B ∧ q.den.bits.length ≤ B
    rw [Nat.size_eq_bits_len,Nat.size_eq_bits_len]
    exact lineInput_cost_width D positive fits i
  obtain ⟨width,work⟩ := BinaryCutPriceSelection.cutScore_charge (lineWithCost D).1.costs (lineOutput a).1 positive stored
  exact ⟨width,Nat.add_le_add work (lineOutput_paid a)⟩

private def selectionBudget {R : Type*} [Semiring R] (n l b : R) : R :=
  2*(l*(2048*((l+1)*(b+1)+1)^2+4)+1+(BinaryEdgeProjection.lineMaskBudget n+2))+
    2048*(l*(b+1)+2)^2+16

attribute [local irreducible] PhysicalSourceReadback.run PhysicalAmplifiedBinaryEdge.run

set_option maxHeartbeats 700000 in
theorem run_polynomial : ∃ p : Polynomial ℕ,
    ∀ {n B : ℕ} (κ : ℕ) (D : Input n) (bits : Bits) (_positive : 1 ≤ B),
      (∀ u v : Fin n, D.costs[u.val][v.val].num.size ≤ B ∧ D.costs[u.val][v.val].den.size ≤ B) →
      ∀ {out : Result (EncodedEdgeSolver.Output n)}, run κ D bits=some out →
        out.paid ≤ p.eval (n+D.demands.length+B+κ) := by
  obtain ⟨q,hq⟩ := PhysicalBinaryEdgeCost.edge_polynomial
  let line : Polynomial ℕ := X*2+X^2
  let budget := selectionBudget X line X
  let setup := lineBudget line X X
  refine ⟨q+q+budget+setup,?_⟩
  intro n B κ D bits positive fits out ran
  let x := n+D.demands.length+B+κ
  have nle : n ≤ x := by dsimp only [x]; omega
  have dle : D.demands.length ≤ x := by dsimp only [x]; omega
  have Ble : B ≤ x := by dsimp only [x]; omega
  have linele : lineSize n ≤ line.eval x := by
    simp only [line,eval_mul,eval_add,eval_X,eval_ofNat,lineSize,pow_two]
    gcongr
  have each (mode : ChargedVertexModes.Mode) (bits : Bits) (r : Result (EncodedEdgeSolver.Output n))
      (yes : one κ mode D bits=some r) : r.paid ≤ q.eval x := by
    obtain ⟨old,performed,rfl⟩ := Option.map_eq_some_iff.mp yes
    exact hq κ D mode bits positive fits performed
  unfold run at ran
  obtain ⟨r,paid,rfl⟩ := Option.map_eq_some_iff.mp ran
  have both := PairedCutSearch.run_paid _ _ _ (each .mass) (each .size) (selection_fields D positive fits) bits paid
  have selection : 2*(BinaryFractionalRows.sumBound (lineSize n) B+(BinaryEdgeProjection.lineMaskBudget n+2))+
      2048*(lineSize n*(B+1)+1+1)^2+16 ≤ budget.eval x := by
    simp only [budget,selectionBudget,BinaryEdgeProjection.lineMaskBudget_eval,eval_add,eval_mul,eval_X,eval_pow,eval_ofNat,eval_one,
      BinaryFractionalRows.sumBound]
    have cmp : lineSize n*(B+1)+1+1 ≤ line.eval x*(x+1)+2 := by rw [Nat.add_assoc]; gcongr
    apply Nat.add_le_add_right _ 16
    apply Nat.add_le_add _ (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left cmp 2))
    have copy := BinaryEdgeProjection.lineMaskBudget_mono nle
    gcongr
  have build := line_paid D positive fits
  have buildBound : lineBudget (lineSize n) D.demands.length B ≤ setup.eval x := by
    simp only [setup,lineBudget,BinaryLineLabels.budget_eval,BinaryLineLabels.assemblyBudget_eval,
      BinaryLineLabels.demandBudget_eval,eval_add,eval_mul,eval_X,eval_ofNat,eval_pow]
    unfold BinaryLineLabels.budget BinaryLineLabels.demandBudget BinaryLineLabels.assemblyBudget
    gcongr
  simp only [eval_add]
  change r.paid+(lineWithCost D).2 ≤ q.eval x+q.eval x+budget.eval x+setup.eval x
  omega

set_option maxHeartbeats 800000 in
theorem wire_polynomial : ∃ p : Polynomial ℕ, ∀ (κ : ℕ) (source tape : Bits)
    {n : ℕ} {r : Result (EncodedEdgeSolver.Output n)},
    (withCost κ source tape).1=some ⟨n,r⟩ →
      (withCost κ source tape).2+r.paid ≤ p.eval (source.length+κ) := by
  obtain ⟨q,hq⟩ := run_polynomial
  let pad : Polynomial ℕ := 3*X+1
  let load := PhysicalBinaryEdgeWire.decodeBudget (X : Polynomial ℕ) X
  refine ⟨ChargedSourceAssembly.parsePolynomial+load+q.comp pad,?_⟩
  intro κ source tape n r ran
  let x := source.length+κ
  simp only [withCost,PhysicalVertexSolver.prepareOn] at ran
  obtain ⟨⟨m,D⟩,parsed,result⟩ := Option.bind_eq_some_iff.mp ran
  obtain ⟨found,once,same⟩ := Option.map_eq_some_iff.mp result
  cases same
  obtain ⟨size,demands,fields⟩ := ChargedSourceAssembly.edge_dimensions parsed
  let G := (PhysicalBinaryEdgeWire.decodeWithCost D).1
  have stored (i : Fin (m*m)) : StoredBounded (BinaryFractionalRows.get D.costs i) source.length := by
    apply fields
    change D.costs[i.val] ∈ D.costs.toList
    have hi : i.val < D.costs.toList.length := by simp only [Vector.length_toList,i.isLt]
    simpa only [Vector.getElem_toList] using List.getElem_mem hi
  have widths (u v : Fin m) :
      G.costs[u.val][v.val].num.size ≤ source.length+1 ∧ G.costs[u.val][v.val].den.size ≤ source.length+1 := by
    let i := finProdFinEquiv (u,v)
    let f := BinaryFractionalRows.get D.costs i
    obtain ⟨a,b⟩ := stored i
    simp only [G,PhysicalBinaryEdgeWire.decode_value,EncodedEdgeInput.decodeInput,Vector.getElem_ofFn,
      BinaryFractionalRows.decode_get]
    change (value f.num).size ≤ _ ∧ (value f.den).size ≤ _
    exact ⟨((Nat.size_le.mpr (value_lt f.num)).trans a).trans (Nat.le_succ _),
      ((Nat.size_le.mpr (value_lt f.den)).trans b).trans (Nat.le_succ _)⟩
  change runOn κ D tape=some found at once
  unfold runOn at once
  obtain ⟨actual,call,rfl⟩ := Option.map_eq_some_iff.mp once
  have length : source.length ≤ x := Nat.le_add_right _ _
  have ys : m+G.demands.length+(source.length+1)+κ ≤ pad.eval x := by
    change m+D.demands.length+(source.length+1)+κ ≤ _
    simp only [pad,eval_mul,eval_add,eval_ofNat,eval_X,eval_one]
    omega
  have both := (hq κ G tape (Nat.le_add_left _ _) widths call).trans (eval_mono q ys)
  have parsing := ((ChargedSourceAssembly.edge_paid source).trans_eq
    (ChargedSourceAssembly.parsePolynomial_eval _).symm).trans
    (eval_mono ChargedSourceAssembly.parsePolynomial length)
  have conversion := (PhysicalBinaryEdgeWire.decode_paid D stored).trans
    (show PhysicalBinaryEdgeWire.decodeBudget m source.length ≤ load.eval x from by
      have hn := size.trans length
      simp only [load,PhysicalBinaryEdgeWire.decodeBudget,eval_add,eval_mul,eval_pow,eval_one,eval_ofNat,eval_X]
      gcongr)
  simp only [eval_add,eval_comp]
  change (ChargedSourceAssembly.edge source).2+(actual.paid+(PhysicalBinaryEdgeWire.decodeWithCost D).2) ≤
    ChargedSourceAssembly.parsePolynomial.eval x+load.eval x+q.eval (pad.eval x)
  omega

end DirectedFlowCutGap.PhysicalPairedEdge
