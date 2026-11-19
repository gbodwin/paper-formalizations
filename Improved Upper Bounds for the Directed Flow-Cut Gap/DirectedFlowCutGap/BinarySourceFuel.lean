import DirectedFlowCutGap.PhysicalSourceDispatch
import DirectedFlowCutGap.BinaryNaturalOperations

/-! Evaluate the dispatcher's existing instruction polynomial by Horner's
rule with measured binary natural arithmetic. The coefficient identity is
checked against the original polynomial definitions below. -/
namespace DirectedFlowCutGap.BinarySourceFuel

open BinaryNaturalOperations Polynomial

private def coefficients : List ℕ :=
  [158836971, 83767673029, 792521540042,
    20368860596477, 223956600367854, 1440824458922991,
    6713751249663725, 25005027356249296, 77510737470540064,
    203535186330542460, 457760948969255328, 886900344087723360,
    1477276770615542016, 2094995548212130176, 2493362359078493184,
    2450106546439382016, 1953391708367241216, 1238612891696332800,
    608993368119705600, 224017368485068800, 58313966144716800,
    9744371888947200, 848701056614400, 18498768076800]

private def form {R : Type*} [Semiring R] (x : R) : List ℕ → R
  | [] => 0
  | c::cs => (c : R)+x*form x cs

set_option maxHeartbeats 3000000 in
private theorem coefficient_identity :
    form (X : Polynomial ℕ) coefficients = PhysicalSourceDispatch.instructionPolynomial := by
  simp only [form,coefficients,PhysicalSourceDispatch.instructionPolynomial,
    FinalDispatchEnvelope.instructionPolynomial,
    FinalDispatchEnvelope.dispatchPolynomial,
    FinalDispatchEnvelope.emptyPolynomial,
    FinalDispatchEnvelope.avoidingPolynomial,
    GridFamilyEnvelope.minimumPolynomial,
    GridFamilyEnvelope.instructionPolynomial,
    GridFamilyEnvelope.prefixPolynomial,
    GridFamilyEnvelope.guessPolynomial,
    GridFamilyEnvelope.wordPolynomial,
    SourcePackingPolynomial.poly_RowVertices_instructionBound,
    SourcePackingPolynomial.poly_PackingParameters_instructionBound,
    SourcePackingPolynomial.poly_ScalarQuotientRow_instructionBound,
    SourcePackingPolynomial.poly_GraphRelaxationProgram_perEntryBound,
    SourcePackingPolynomial.poly_GraphRelaxationProgram_instructionBound,
    SourcePackingPolynomial.poly_GraphDiscoveryProgram_passBudget,
    SourcePackingPolynomial.poly_GraphDiscoveryProgram_roundBudget,
    SourcePackingPolynomial.poly_GraphDiscoveryProgram_roundWidth,
    SourcePackingPolynomial.poly_GraphDiscoveryProgram_discoveryWidth,
    SourcePackingPolynomial.poly_GraphDiscoveryProgram_lookupBudget,
    SourcePackingPolynomial.poly_GraphDiscoveryProgram_discoveryBudget,
    SourcePackingPolynomial.poly_SupportRecoveryProgram_scanCap,
    SourcePackingPolynomial.poly_SupportRecoveryProgram_searchCap,
    SourcePackingPolynomial.poly_CanonicalRationalSum_instructionBound,
    SourcePackingPolynomial.poly_MaterializedPathSum_instructionBound,
    SourcePackingPolynomial.poly_CostedSupportProgram_recoveryCap,
    SourcePackingPolynomial.poly_GraphRecoveryController_instructionBound,
    SourcePackingPolynomial.poly_DemandCollection_instructionBound,
    SourcePackingPolynomial.poly_OracleMask_instructionBound,
    SourcePackingPolynomial.poly_CapacityBottleneck_instructionBound,
    SourcePackingPolynomial.poly_GraphOracleMachine_instructionBound,
    SourcePackingPolynomial.poly_PackingStart_initialWidth,
    SourcePackingPolynomial.poly_NormalizedRow_scalarWidth,
    SourcePackingPolynomial.poly_NormalizedRow_instructionBound,
    SourcePackingPolynomial.poly_ObjectiveProductList_instructionBound,
    SourcePackingPolynomial.poly_ObjectiveRow_instructionBound,
    SourcePackingPolynomial.poly_PackingStart_bestWidth,
    SourcePackingPolynomial.poly_PackingStart_instructionBound,
    SourcePackingPolynomial.poly_PackingGuard_objectiveWidth,
    SourcePackingPolynomial.poly_PackingGuard_instructionBound,
    SourcePackingPolynomial.poly_AdaptivePackingState_normalizedWidth,
    SourcePackingPolynomial.poly_PackingEntry_instructionBound,
    SourcePackingPolynomial.poly_PackingUpdateRow_instructionBound,
    SourcePackingPolynomial.poly_PackingLoadRow_entryBound,
    SourcePackingPolynomial.poly_PackingLoadRow_instructionBound,
    SourcePackingPolynomial.poly_AdaptivePackingState_instructionBound,
    SourcePackingPolynomial.poly_PackingIteration_smallWidth,
    SourcePackingPolynomial.poly_PackingIteration_commonWidth,
    SourcePackingPolynomial.poly_PackingIteration_instructionBound,
    SourcePackingPolynomial.poly_PackingRun_startWidth,
    SourcePackingPolynomial.poly_PackingRun_instructionBound,
    SourcePackingPolynomial.poly_PackingComplete_parameterWidth,
    SourcePackingPolynomial.poly_PackingComplete_instructionBound,
    SourcePackingPolynomial.poly_PreparedPacking_instructionBound,
    SourcePackingPolynomial.poly_EnumeratedPacking_instructionBound]
  ring

private theorem form_eval (x : ℕ) (cs : List ℕ) : (form (X : Polynomial ℕ) cs).eval x=form x cs := by
  induction cs with
  | nil => simp [form]
  | cons c cs ih => simp only [form,eval_add,eval_natCast,eval_mul,eval_X,ih,Nat.cast_id]

private def horner (x : ℕ) : List ℕ → ℕ × ℕ
  | [] => (0,4)
  | c::cs =>
    let rest := horner x cs
    let product := BinaryNaturalOperations.mul x rest.1
    let sum := BinaryNaturalOperations.add c product.1
    (sum.1,rest.2+product.2+sum.2+8)

private theorem horner_value (x : ℕ) (cs : List ℕ) : (horner x cs).1=form x cs := by
  induction cs with
  | nil => rfl
  | cons c cs ih => simp only [horner,form,BinaryNaturalOperations.add_value,
      BinaryNaturalOperations.mul_value,ih,Nat.cast_id]

private theorem horner_paid {x W : ℕ} (xPos : 1 ≤ x) (width : x ≤ W) (cs : List ℕ)
    (whole : form x cs ≤ W) : (horner x cs).2 ≤ cs.length*(2*BinaryRawRational.budget W+16)+4 := by
  induction cs with
  | nil => simp [horner]
  | cons c cs ih =>
    have total : c+x*form x cs ≤ W := whole
    let r := horner x cs
    let z := BinaryNaturalOperations.mul x r.1
    let s := BinaryNaturalOperations.add c z.1
    have w : form x cs ≤ W := by
      have product := Nat.mul_le_mul_right (form x cs) xPos
      rw [Nat.one_mul] at product
      omega
    have subwork : r.2 ≤ _ := ih w
    have hw : r.1 ≤ W := (horner_value x cs).symm ▸ w
    have cfit : c.size ≤ W := (size_le_self c).trans (by omega)
    have pfit : z.1.size ≤ W := by
      rw [show z.1=x*form x cs from (BinaryNaturalOperations.mul_value _ _).trans
        (congrArg (x*·) (horner_value x cs))]
      exact (size_le_self _).trans (by omega)
    have prod : z.2 ≤ BinaryRawRational.budget W+4 := BinaryNaturalOperations.mul_paid
      ((size_le_self x).trans width) ((size_le_self r.1).trans hw)
    have sum : s.2 ≤ BinaryRawRational.budget W+4 := BinaryNaturalOperations.add_paid cfit pfit
    simp only [List.length_cons,Nat.add_mul,Nat.one_mul]
    change r.2+z.2+s.2+8 ≤ _
    omega

def compute (length : ℕ) : ℕ × ℕ :=
  let total := horner length coefficients
  let fuel := BinaryNaturalOperations.add total.1 1
  (fuel.1,fuel.2+total.2+12*(length+1)^2+8)

theorem fuel_value (length : ℕ) :
    (compute length).1=PhysicalSourceDispatch.instructionPolynomial.eval length+1 := by
  simp only [compute,BinaryNaturalOperations.add_value,horner_value,← form_eval,coefficient_identity]

theorem length_le (length : ℕ) : length ≤ PhysicalSourceDispatch.instructionPolynomial.eval length := by
  simp only [PhysicalSourceDispatch.instructionPolynomial,eval_add,eval_mul,eval_X,eval_ofNat]
  omega

def budget {R : Type*} [Semiring R] (bound : R) : R :=
  24*(2*BinaryRawRational.budget (bound+1)+16)+BinaryRawRational.budget (bound+1)+12*(bound+1)^2+20

theorem budget_mono {B C : ℕ} (h : B ≤ C) : budget B ≤ budget C := by
  unfold budget BinaryRawRational.budget
  gcongr

theorem budget_eval (bound : Polynomial ℕ) (x : ℕ) :
    (budget bound).eval x=budget (bound.eval x) := by
  simp only [budget,BinaryRawRational.budget,eval_add,eval_mul,eval_pow,eval_one,eval_ofNat]

set_option maxHeartbeats 1000000 in
theorem compute_paid {length : ℕ} (h : 1 ≤ length) :
    (compute length).2 ≤ budget (PhysicalSourceDispatch.instructionPolynomial.eval length) := by
  let W := PhysicalSourceDispatch.instructionPolynomial.eval length
  let total := horner length coefficients
  let fuel := BinaryNaturalOperations.add total.1 1
  have lengthW := length_le length
  have val : form length coefficients=W := by rw [← form_eval,coefficient_identity]
  have hv : total.1 = W := (horner_value length coefficients).trans val
  have totalBound : total.2 ≤ 24*(2*BinaryRawRational.budget (W+1)+16)+4 := by
    have width : length ≤ W+1 := lengthW.trans (Nat.le_succ W)
    have limit : form length coefficients ≤ W+1 := by rw [val]; exact Nat.le_succ W
    have paid := horner_paid h width coefficients limit
    exact paid
  have fuelWidth : total.1.size ≤ W+1 := by rw [hv]; exact (size_le_self W).trans (Nat.le_succ W)
  have fuelBound : fuel.2 ≤ BinaryRawRational.budget (W+1)+4 :=
    BinaryNaturalOperations.add_paid fuelWidth ((size_le_self 1).trans (by omega))
  have framing : 12*(length+1)^2 ≤ 12*(W+1)^2 := by gcongr
  change fuel.2+total.2+12*(length+1)^2+8 ≤ budget W
  unfold budget
  omega

end DirectedFlowCutGap.BinarySourceFuel
