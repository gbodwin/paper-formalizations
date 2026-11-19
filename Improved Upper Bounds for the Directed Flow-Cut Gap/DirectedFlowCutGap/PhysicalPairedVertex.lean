import DirectedFlowCutGap.PairedCutSearch
import DirectedFlowCutGap.PhysicalAmplifiedBinaryVertex

/-! Both approximation modes run on one tape. The price comparison is on
the original vertex costs and uses the returned masks. -/
namespace DirectedFlowCutGap.PhysicalPairedVertex

open BinaryArithmetic FiniteDrawTrees FiniteAmplification Polynomial
open EncodedVertexAmplification
open PhysicalIntegerRoundingCost (eval_mono)
open PairedCutSearch (Result)

private def one {n : ℕ} (κ : ℕ) (mode : ChargedVertexModes.Mode)
    (D : BinaryFractionalGuesses.Input n) (bits : Bits) :
    Option (Result (EncodedVertexSolver.Output n)) :=
  (PhysicalAmplifiedBinaryVertex.vertex κ mode D bits).map fun r =>
    ⟨r.output,r.suffix,r.dispatch+r.readback+r.roundingAndSelection⟩

private theorem one_observe {n : ℕ} (κ : ℕ) (mode : ChargedVertexModes.Mode)
    (D : BinaryFractionalGuesses.Input n) (bits : Bits) :
    (one κ mode D bits).map Result.observe=PairedCutSearch.observeTape
      (polynomialBitTree κ (BinaryFractionalGuesses.decodeInput D) (ChargedVertexModes.round n mode)) bits := by
  have eq := (PhysicalAmplifiedBinaryVertex.vertex_observe κ mode D bits).trans
    (PhysicalAmplifiedVertexSolver.vertex_observe κ mode D bits)
  unfold one
  rw [Option.map_map]
  exact eq

def run {n : ℕ} (κ : ℕ) (D : BinaryFractionalGuesses.Input n) (bits : Bits) :=
  PairedCutSearch.run (BinaryCutPriceSelection.cutScore D.costs) (one κ .mass D) (one κ .size D) bits

def tree {n : ℕ} (κ : ℕ) (D : BinaryFractionalGuesses.Input n) :
    FiniteDrawTrees.Tree (EncodedVertexSolver.Output n) :=
  let G := BinaryFractionalGuesses.decodeInput D
  PairedCutSearch.tree (BinaryCutPriceSelection.cutScore D.costs)
    (polynomialBitTree κ G EncodedWeightedRounding.tree) (polynomialBitTree κ G EncodedSizeRounding.tree)

def tapeBudget {n : ℕ} (κ : ℕ) (D : BinaryFractionalGuesses.Input n) : ℕ :=
  2*EncodedSolverBits.vertexBudget κ (BinaryFractionalGuesses.decodeInput D)

theorem run_observe {n : ℕ} (κ : ℕ) (D : BinaryFractionalGuesses.Input n) (bits : Bits) :
    (run κ D bits).map Result.observe=PairedCutSearch.observeTape (tree κ D) bits :=
  PairedCutSearch.run_observe _ _ _ _ _ (one_observe κ .mass D) (one_observe κ .size D) bits

theorem tree_within {n : ℕ} (κ : ℕ) (D : BinaryFractionalGuesses.Input n) :
    Within (tapeBudget κ D) (tree κ D) := by
  let G := BinaryFractionalGuesses.decodeInput D
  simpa only [tree,tapeBudget,two_mul] using
    PairedCutSearch.tree_within (EncodedSolverBits.vertex_mass_within κ G)
      (EncodedSolverBits.vertex_size_within κ G) (BinaryCutPriceSelection.cutScore D.costs)

theorem tree_binary {n : ℕ} (κ : ℕ) (D : BinaryFractionalGuesses.Input n) :
    LazyFairBitTrees.Binary (tree κ D) :=
  PairedCutSearch.tree_binary (bitTree_binary ..) (bitTree_binary ..) _

theorem support_valid {n : ℕ} (κ : ℕ) (D : BinaryFractionalGuesses.Input n)
    {out : EncodedVertexSolver.Output n} (h : out ∈ (ideal (tree κ D)).support) :
    EncodedVertexSolver.Valid (BinaryFractionalGuesses.decodeInput D) out := by
  rcases PairedCutSearch.support _ _ _ h with hm | hs
  · exact massBit_support_valid _ _ _ hm
  · exact sizeBit_support_valid _ _ _ hs

theorem fairTape {n : ℕ} (κ : ℕ) (D : BinaryFractionalGuesses.Input n) :
    (EncodedSolverBits.fairTape (tapeBudget κ D)).map (fun bits => (run κ D bits).map Result.output) =
      (ideal (tree κ D)).map some :=
  PairedCutSearch.fairTape (run κ D) (tree κ D) (run_observe κ D) (tree_within κ D) (tree_binary κ D)

def withCost (κ : ℕ) (source tape : Bits) :
    PhysicalCoverAccess.Read (Σ n,Result (EncodedVertexSolver.Output n)) :=
  let parsed := ChargedSourceAssembly.vertex source
  (PhysicalVertexSolver.prepareOn (fun _ input => run κ input tape) parsed.1,parsed.2)

theorem complete {n : ℕ} (κ : ℕ) (D : BinaryFractionalGuesses.Input n) (source tape : Bits)
    (parsed : EncodedVertexInput.parse source=some ⟨n,D⟩) (enough : tapeBudget κ D ≤ tape.length) :
    ∃ r used, (withCost κ source tape).1=some ⟨n,r⟩ ∧ r.suffix=tape.drop used ∧
      used≤tapeBudget κ D ∧ EncodedVertexSolver.Valid (BinaryFractionalGuesses.decodeInput D) r.output := by
  obtain ⟨r,k,ok,tail,length,valid⟩ := PairedCutSearch.complete (run κ D) (tree κ D)
    (run_observe κ D) (tree_within κ D) (tree_binary κ D) (fun _ => support_valid κ D) tape enough
  refine ⟨r,k,?_,tail,length,valid⟩
  simp only [withCost,ChargedSourceAssembly.vertex_value]
  exact PhysicalVertexSolver.prepareOn_eq (fun _ input => run κ input tape) parsed ok

private theorem mode_failure {n : ℕ} (κ : ℕ) (G : EncodedVertexSolver.GraphInput n)
    (mode : EncodedVertexSolver.Rounding n)
    (within : ∀ input, Within (roundDrawBound n) (mode input)) (B : ℝ) (hB : 0 ≤ B)
    (bound : EncodedVertexSolver.expectedPrice G mode ≤ B) :
    probability (ideal (polynomialBitTree κ G mode)) (fun out => 2*B < EncodedVertexSolver.outputPrice G out) ≤
      ((max 1 n : ℕ) : ℝ) ^ (-(κ : ℝ)) := by
  rcases hB.eq_or_lt with eq | pos
  · subst B
    rw [mul_zero,PairedCutSearch.probability_gt_zero_eq_zero]
    · positivity
    · exact fun _ h => bounded_zero_price_on_support _ _ _ G mode bound h
  · exact polynomial_failure_le κ G mode within B pos bound

theorem failure_min {n : ℕ} (κ : ℕ) (D : BinaryFractionalGuesses.Input n) (mass size : ℝ)
    (hm : 0 ≤ mass) (hs : 0 ≤ size)
    (em : EncodedVertexSolver.expectedPrice (BinaryFractionalGuesses.decodeInput D) EncodedWeightedRounding.tree ≤ mass)
    (es : EncodedVertexSolver.expectedPrice (BinaryFractionalGuesses.decodeInput D) EncodedSizeRounding.tree ≤ size) :
    probability (ideal (tree κ D))
      (fun out => min (2*mass) (2*size) < EncodedVertexSolver.outputPrice (BinaryFractionalGuesses.decodeInput D) out) ≤
      ((max 1 n : ℕ) : ℝ) ^ (-(κ : ℝ)) := by
  let G := BinaryFractionalGuesses.decodeInput D
  have price (a : EncodedVertexSolver.Output n) :
      ((BinaryRational.decode (BinaryCutPriceSelection.cutScore D.costs a).1).realValue : ℝ)=
      EncodedVertexSolver.outputPrice G a := by
    rw [BinaryCutPriceSelection.cutScore_decodes,codePrice_value]
  exact PairedCutSearch.failure_min _ _ _ _ price
    (mode_failure κ G _ EncodedWeightedRounding.tree_within mass hm em)
    (mode_failure κ G _ EncodedSizeRounding.tree_within size hs es)

open scoped NNReal in
theorem approximation_uniform :
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
      ∀ (n κ : ℕ) (D : BinaryFractionalGuesses.Input n) (w : Fin n → ℝ≥0),
        let G := BinaryFractionalGuesses.decodeInput D
        IsFractionalCut G.graph w {d | d ∈ G.demands} →
        probability (ideal (tree κ D)) (fun a =>
          C*min ((n : ℝ)^ε*(totalWeight w : ℝ)^(1/2 : ℝ)) ((n : ℝ)^(1/3+ε))*
            (weightedCost (EncodedVertexSolver.capacity G) w : ℝ) <
              EncodedVertexSolver.outputPrice G a) ≤ ((max 1 n : ℕ) : ℝ)^(-(κ : ℝ)) := by
  intro ε hε
  obtain ⟨M,hM,mass⟩ := EncodedVertexSolver.mass_expected_uniform ε hε
  obtain ⟨S,_hS,size⟩ := EncodedVertexSolver.size_expected_uniform ε hε
  let C := max M S
  have pos : 0 < C := hM.trans_le (le_max_left _ _)
  refine ⟨2*C,by positivity,?_⟩
  intro n κ D w G valid
  let m := (n : ℝ)^ε*(totalWeight w : ℝ)^(1/2 : ℝ)
  let s := (n : ℝ)^(1/3+ε)
  let q := (weightedCost (EncodedVertexSolver.capacity G) w : ℝ)
  have em : EncodedVertexSolver.expectedPrice G EncodedWeightedRounding.tree ≤ C*m*q := by
    apply (mass n G w valid).trans
    change M*(n : ℝ)^ε*(totalWeight w : ℝ)^(1/2 : ℝ)*q ≤ _
    rw [mul_assoc M]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)) (by positivity)
  have es : EncodedVertexSolver.expectedPrice G EncodedSizeRounding.tree ≤ C*s*q :=
    (size n G w valid).trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_right _ _)
      (by positivity)) (by positivity))
  have result := failure_min κ D (C*m*q) (C*s*q) (by positivity) (by positivity) em es
  rw [PairedCutSearch.scaled_min pos.le (by positivity : 0 ≤ q)] at result
  exact result

private noncomputable def selectionPolynomial : Polynomial ℕ :=
  let row := X*(2048*((X+1)*(X+1)+1)^2+4)+1
  2*row+2048*(X*(X+1)+2)^2+16

theorem run_polynomial : ∃ p : Polynomial ℕ, ∀ {n : ℕ} (κ : ℕ) (D : BinaryFractionalGuesses.Input n)
    (bits : Bits) {out : Result (EncodedVertexSolver.Output n)}, run κ D bits=some out →
    out.paid ≤ p.eval (PhysicalSolverCostEnvelope.vertexSize D κ) := by
  obtain ⟨q,hq⟩ := PhysicalAmplifiedBinaryVertex.vertex_polynomial
  refine ⟨q+q+selectionPolynomial,?_⟩
  intro n κ D bits out ran
  let B := ChargedVertexModes.priceWidth D
  let x := PhysicalSolverCostEnvelope.vertexSize D κ
  have nle : n ≤ x := by dsimp only [x,PhysicalSolverCostEnvelope.vertexSize]; omega
  have Ble : B ≤ x := by dsimp only [x,B,PhysicalSolverCostEnvelope.vertexSize]; omega
  have each (mode : ChargedVertexModes.Mode) (bits : Bits) (r : Result (EncodedVertexSolver.Output n))
      (yes : one κ mode D bits=some r) : r.paid ≤ q.eval x := by
    obtain ⟨old,performed,rfl⟩ := Option.map_eq_some_iff.mp yes
    exact hq κ mode D bits performed
  have scores := fun a => BinaryCutPriceSelection.cutScore_charge D.costs a
    (ChargedVertexModes.priceWidth_positive D) (ChargedVertexModes.priceWidth_bounds D)
  have bound := PairedCutSearch.run_paid _ _ _ (each .mass) (each .size) scores bits ran
  rw [eval_add,eval_add]
  apply bound.trans
  have sp : 2*BinaryFractionalRows.sumBound n B+2048*(n*(B+1)+1+1)^2+16 ≤ selectionPolynomial.eval x := by
    simp only [selectionPolynomial,eval_add,eval_mul,eval_X,eval_one,eval_pow,eval_ofNat,
      BinaryFractionalRows.sumBound]
    have cmp : n*(B+1)+1+1 ≤ x*(x+1)+2 := by rw [Nat.add_assoc]; gcongr
    apply Nat.add_le_add_right _ 16
    apply Nat.add_le_add _ (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left cmp 2))
    gcongr
  change q.eval x+q.eval x+2*BinaryFractionalRows.sumBound n B+2048*(n*(B+1)+1+1)^2+16 ≤
    q.eval x+q.eval x+selectionPolynomial.eval x
  omega

theorem wire_polynomial : ∃ p : Polynomial ℕ, ∀ (κ : ℕ) (source tape : Bits)
    {n : ℕ} {r : Result (EncodedVertexSolver.Output n)},
    (withCost κ source tape).1=some ⟨n,r⟩ →
      (withCost κ source tape).2+r.paid ≤ p.eval (source.length+κ) := by
  let withPhases {m : ℕ} (κ : ℕ) (_ : ChargedVertexModes.Mode) (D : BinaryFractionalGuesses.Input m)
      (bits : Bits) : Option (PhysicalAmplifiedVertexSolver.Result m) :=
    (run κ D bits).map fun a => ⟨a.output,a.suffix,0,0,a.paid⟩
  have bounds : ∃ p : Polynomial ℕ, ∀ {m : ℕ} (κ : ℕ) mode
      (D : BinaryFractionalGuesses.Input m) (bits : Bits) {r : PhysicalAmplifiedVertexSolver.Result m},
      withPhases κ mode D bits=some r →
      r.dispatch+r.readback+r.roundingAndSelection ≤ p.eval (PhysicalSolverCostEnvelope.vertexSize D κ) := by
    obtain ⟨p,hp⟩ := run_polynomial
    refine ⟨p,?_⟩
    intro m κ mode D bits a ran
    obtain ⟨found,call,rfl⟩ := Option.map_eq_some_iff.mp ran
    simpa only [Nat.zero_add] using hp κ D bits call
  obtain ⟨p,hp⟩ := PhysicalWireCostEnvelope.vertex_wire_polynomial_for @withPhases bounds
  refine ⟨p,?_⟩
  intro κ source tape n r ran
  obtain ⟨⟨m,D⟩,parsed,result⟩ := Option.bind_eq_some_iff.mp ran
  obtain ⟨found,once,same⟩ := Option.map_eq_some_iff.mp result
  cases same
  have call : withPhases κ .mass D tape=some ⟨r.output,r.suffix,0,0,r.paid⟩ := by
    simp only [withPhases,once,Option.map_some]
  have entry := PhysicalVertexSolver.prepareOn_eq (fun _ input => withPhases κ .mass input tape) parsed call
  simpa only [withCost,Nat.zero_add,Nat.add_zero] using hp κ .mass source tape entry

end DirectedFlowCutGap.PhysicalPairedVertex
