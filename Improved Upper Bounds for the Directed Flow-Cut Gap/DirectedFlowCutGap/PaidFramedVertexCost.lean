import DirectedFlowCutGap.PaidFramedVertexWire
import DirectedFlowCutGap.PaidVertexRoundingCost
import DirectedFlowCutGap.PaidVertexAmplificationCost
namespace DirectedFlowCutGap.PaidFramedVertexWire

open BinaryArithmetic BinaryRational Polynomial
open PhysicalSolverCostEnvelope EncodedVertexAmplification
open ChargedPhysicalVertexSolver (trialLimit)
open PhysicalIntegerRoundingCost (eval_mono)
open PhysicalCoverAccess (Read)

attribute [local irreducible] run PhysicalSourceInputJoin.vertex

set_option maxHeartbeats 1600000 in
theorem run_polynomial : ∃ p : Polynomial ℕ, ∀ {n : ℕ} (κ : ℕ) (mode : ChargedVertexModes.Mode)
    (D : BinaryFractionalGuesses.Input n) (tape : Bits), (run κ mode D tape).2 ≤ p.eval (vertexSize D κ) := by
  obtain ⟨q,hq⟩ := PaidVertexRounding.polynomial_bound
  obtain ⟨p,hp⟩ := PaidVertexAmplification.polynomial_on_rows q
  let wire : Polynomial ℕ := 2*(X+X*X+X*(X+X))+3*(X+X+X)+3
  let exponent : Polynomial ℕ := (X+2)*X+1
  let pad := X+wire+exponent+drawPolynomial X
  let inst := PhysicalSourceDispatch.instructionPolynomial
  let lookup := PhysicalSourceReadback.planBound (1+inst) inst
  let phases := PhysicalSourceDispatch.paidPolynomial+lookup+p
  refine ⟨phases.comp pad+BinarySolverOuterControls.budget X X,?_⟩
  intro n κ mode D tape
  let y := vertexSize D κ
  let x := pad.eval y
  let z := trialEnvelope.eval x+x
  let e := confidenceExponent n κ
  let B := ChargedVertexModes.priceWidth D
  let T := trialLimit (BinaryFractionalGuesses.decodeInput D) (roundDrawBound n) e (e+1)
  have hy : y ≤ x := by simp only [x,pad,eval_add,eval_X]; omega
  have hx : x ≤ z := Nat.le_add_left _ _
  have hn : n ≤ y := by dsimp only [y,vertexSize]; omega
  have hb : B ≤ y := by dsimp only [B,y,vertexSize]; omega
  have hd : D.demands.length ≤ y := by dsimp only [y,vertexSize]; omega
  have confidence : κ ≤ y := by dsimp only [y,vertexSize]; omega
  have he : e+1 ≤ x := by
    have h := Nat.add_le_add_right ((exponent_le n κ).trans (Nat.mul_le_mul (Nat.add_le_add_right hn 2) confidence)) 1
    have next : exponent.eval y ≤ x := by simp only [x,pad,eval_add,eval_X]; omega
    simp only [exponent,eval_add,eval_mul,eval_ofNat,eval_X,eval_one] at next
    exact h.trans next
  have draw : roundDrawBound n ≤ x := by
    have bound : (drawPolynomial X).eval y ≤ x := by simp only [x,pad,eval_add,eval_X]; omega
    rw [drawPolynomial_eval,eval_X] at bound
    unfold roundDrawBound EncodedUniformRounding.drawBound at bound ⊢
    exact (show ((6*(4*n^2))^3+2)*(2*(6*(4*n^2))*(6*(4*n^2))) ≤
      ((6*(4*y^2))^3+2)*(2*(6*(4*y^2))*(6*(4*y^2))) by gcongr).trans bound
  have source : (PhysicalSourceDispatch.input D).length ≤ x := by
    have bound : wire.eval y ≤ x := by simp only [x,pad,eval_add,eval_X]; omega
    apply (PhysicalSourceSizeBounds.source_size_le D).trans
    apply le_trans ?_ bound
    simp only [wire,eval_add,eval_mul,eval_ofNat,eval_X,PhysicalSourceSizeBounds.sourceSizeBound]
    have stored : LambdaRowProgram.rowBits D.costs.toList ≤ y := (Nat.le_add_right _ 1).trans hb
    gcongr
  have positive := ChargedVertexModes.priceWidth_positive D
  have fits := ChargedVertexModes.priceWidth_bounds D
  have eBound : e ≤ x := (Nat.le_succ _).trans he
  have ht : T ≤ z := (trialLimit_le D (roundDrawBound n) e (e+1) (hn.trans hy) (hb.trans hy)
    draw eBound he fits).trans (Nat.le_add_right _ _)
  obtain ⟨dispatch,reader,hdx,hrx,observed⟩ := run_paid κ mode D tape
  let plan := PhysicalCoverReader.plan (BinaryFractionalGuesses.solveInput D).1
  have work := hp D (PaidVertexRounding.runner mode) (roundDrawBound n) e (e+1) plan dispatch reader tape
    (hn.trans hy) (hb.trans hy) draw eBound he positive fits (ChargedPhysicalVertexSolver.rowsCount_le D)
    (fun rows stored row member bits => by
      apply hq ((hn.trans hy).trans hx) ht _ mode _ (VertexReductionWidths.fractional_input D stored member) bits
      have H := eval_mono PhysicalSourceDispatch.instructionPolynomial (source.trans hx)
      have price := (hb.trans hy).trans hx
      exact max_le (by omega) (by omega))
  have dispatchWork := hdx.trans (eval_mono PhysicalSourceDispatch.paidPolynomial source)
  have readerWork : reader ≤ lookup.eval x := by
    apply hrx.trans
    simp only [lookup,PhysicalSourceReadback.planBound_eval,eval_add,eval_one]
    exact PhysicalSourceReadback.planBound_mono (Nat.add_le_add_left (eval_mono _ source) 1) (eval_mono _ source)
  have meter := (BinarySolverOuterControls.vertex_paid n κ).trans (BinarySolverOuterControls.budget_mono hn confidence)
  rw [BinarySolverOuterControls.vertex_draws,BinarySolverOuterControls.vertex_extra,BinarySolverOuterControls.vertex_confidence] at observed
  rw [observed]
  simp only [eval_add,eval_comp,BinarySolverOuterControls.budget_eval,eval_X,phases]
  change (BinarySolverOuterControls.vertex n κ).paid+dispatch+reader+
    (PaidVertexAmplification.runWithPlan D (PaidVertexRounding.runner mode) (roundDrawBound n) e (e+1)
      plan dispatch reader tape).2 ≤ PhysicalSourceDispatch.paidPolynomial.eval x+lookup.eval x+p.eval x+
        BinarySolverOuterControls.budget y y
  exact (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add meter dispatchWork) readerWork) work).trans_eq (by ac_rfl)

private theorem rowBits_le {x : ℕ} (qs : List Fraction) (fits : ∀ q ∈ qs, StoredBounded q x) :
    LambdaRowProgram.rowBits qs ≤ qs.length*(x+x) := by
  induction qs with
  | nil => simp [LambdaRowProgram.rowBits]
  | cons q qs ih =>
      obtain ⟨a,b⟩ := fits q List.mem_cons_self
      have more := ih (fun r hr => fits r (List.mem_cons_of_mem _ hr))
      simp only [LambdaRowProgram.rowBits,List.length_cons,Nat.add_mul,Nat.one_mul]
      omega

set_option maxHeartbeats 1200000 in
theorem wire_polynomial : ∃ p : Polynomial ℕ, ∀ (κ : ℕ) (mode : ChargedVertexModes.Mode) (source tape : Bits),
    (vertexWithCost κ mode source tape).2 ≤ p.eval (source.length+κ) := by
  obtain ⟨p,hp⟩ := run_polynomial
  let pad : Polynomial ℕ := X+X+1+C 2*X^2+X
  refine ⟨PhysicalSourceInputJoin.parsePolynomial+p.comp pad,?_⟩
  intro κ mode source tape
  let x := source.length+κ
  have hS : source.length ≤ x := Nat.le_add_right _ _
  have confidence : κ ≤ x := Nat.le_add_left _ _
  have parse := ((PhysicalSourceInputJoin.vertex_paid source).trans_eq
    (PhysicalSourceInputJoin.parsePolynomial_eval _).symm).trans (eval_mono _ hS)
  rw [eval_add,eval_comp]
  unfold vertexWithCost
  apply Read.bind_bound parse
  rintro ⟨n,D⟩ stored
  have found : (ChargedSourceAssembly.vertex source).1=some ⟨n,D⟩ := by
    rwa [ChargedSourceAssembly.vertex_value,← PhysicalSourceInputJoin.vertex_value]
  obtain ⟨size,demands,fields⟩ := ChargedSourceAssembly.vertex_dimensions found
  have width := rowBits_le D.costs.toList fields
  rw [Vector.length_toList] at width
  have padded : vertexSize D κ ≤ pad.eval x := by
    simp only [pad,eval_add,eval_mul,eval_pow,eval_C,eval_X,eval_one,vertexSize,ChargedVertexModes.priceWidth]
    have hn := size.trans hS
    have w := width.trans (show n*(source.length+source.length) ≤ x*(x+x) by gcongr)
    nlinarith [size.trans hS,demands.trans hS]
  exact (hp κ mode D tape).trans (eval_mono p padded)

noncomputable def serializedLengthBound : Polynomial ℕ := 10*X^2+9*X+3

theorem serialized_length_le {n : ℕ} {D : BinaryFractionalGuesses.Input n} {source : Bits}
    (accepted : (PhysicalSourceInputJoin.vertex source).1=some ⟨n,D⟩) :
    (PhysicalSourceDispatch.input D).length ≤ serializedLengthBound.eval source.length := by
  let width := source.length
  have original : (ChargedSourceAssembly.vertex source).1=some ⟨n,D⟩ := by
    simpa only [ChargedSourceAssembly.vertex_value, ← PhysicalSourceInputJoin.vertex_value] using accepted
  obtain ⟨nLe,dLe,fields⟩ := ChargedSourceAssembly.vertex_dimensions original
  have rows := rowBits_le D.costs.toList fields
  rw [Vector.length_toList] at rows
  have rowsWide : LambdaRowProgram.rowBits D.costs.toList ≤ 2*width^2 := by
    refine rows.trans ?_
    calc
      n*(source.length+source.length) ≤ width*(width+width) := Nat.mul_le_mul_right _ nLe
      _ = 2*width^2 := by ring
  refine (PhysicalSourceSizeBounds.source_size_le D).trans ?_
  calc
    _ ≤ PhysicalSourceSizeBounds.sourceSizeBound width width (2*width^2) := by
      unfold PhysicalSourceSizeBounds.sourceSizeBound
      gcongr
    _ = serializedLengthBound.eval source.length := by
      simp only [PhysicalSourceSizeBounds.sourceSizeBound,serializedLengthBound,
        eval_add,eval_mul,eval_pow,eval_ofNat,eval_X]
      ring

/-- The physical parser and the counted fractional source controller use a
polynomial amount of recorded work on each original source, including a
malformed source that returns before dispatch. -/
theorem fractional_source_polynomial : ∃ p : Polynomial ℕ, ∀ source : Bits,
    let parsed := PhysicalSourceInputJoin.vertex source
    parsed.2 + ((parsed.1.map fun ⟨_, D⟩ =>
      let work := PhysicalSourceReadback.runWithBitCharges D
      work.1.2 + work.2).getD 0) ≤ p.eval source.length := by
  obtain ⟨p, paid⟩ := PhysicalSourceReadback.bitCharges_polynomial
  refine ⟨PhysicalSourceInputJoin.parsePolynomial+p.comp serializedLengthBound, ?_⟩
  intro source
  let parsed := PhysicalSourceInputJoin.vertex source
  let width := source.length
  have parse : parsed.2≤PhysicalSourceInputJoin.parsePolynomial.eval width :=
    (PhysicalSourceInputJoin.vertex_paid source).trans_eq (PhysicalSourceInputJoin.parsePolynomial_eval width).symm
  rw [eval_add,eval_comp]
  change parsed.2 + ((parsed.1.map fun ⟨_, D⟩ =>
    let work := PhysicalSourceReadback.runWithBitCharges D
    work.1.2 + work.2).getD 0) ≤ _
  apply Nat.add_le_add parse
  cases accepted : parsed.1 with
  | none => exact Nat.zero_le _
  | some stored =>
      obtain ⟨n,D⟩ := stored
      exact (paid D).trans (eval_mono p (serialized_length_le accepted))

private theorem joined_framingBudget_eval (s : ℕ) :
    (PhysicalSourceInputJoin.framingBudget (X : Polynomial ℕ)).eval s =
      PhysicalSourceInputJoin.framingBudget s := by
  simp only [PhysicalSourceInputJoin.framingBudget,eval_X,eval_add,eval_mul,eval_pow,eval_ofNat,eval_one]

private def vertexWithFramedRun
    (runner : {n : ℕ} → ℕ → ChargedVertexModes.Mode → BinaryFractionalGuesses.Input n → Bits →
      Read (PhysicalAmplifiedVertexSolver.Result n) × ℕ)
    (κ : ℕ) (mode : ChargedVertexModes.Mode) (source tape : Bits) :
    Read (Σ n,PhysicalAmplifiedVertexSolver.Result n) × (ℕ × ℕ) :=
  let parsed := PhysicalSourceInputJoin.vertexWithFramingRecords source
  let executed : Read (Σ n,PhysicalAmplifiedVertexSolver.Result n) × ℕ := match parsed.1.1 with
    | none => ((none,parsed.1.2),0)
    | some ⟨n,D⟩ =>
        let r := runner κ mode D tape
        ((r.1.1.map (fun out => ⟨n,out⟩),parsed.1.2+r.1.2),r.2)
  (executed.1,(executed.2,parsed.2))

/-- Retain both the framer record count and the cached fractional source
work from the same paid vertex execution. -/
def vertexWithJoinedWork (κ : ℕ) (mode : ChargedVertexModes.Mode) (source tape : Bits) :
    Read (Σ n,PhysicalAmplifiedVertexSolver.Result n) × (ℕ × ℕ) :=
  vertexWithFramedRun runWithCacheWork κ mode source tape

/-- Run the original typed input with the measured terminal reader and
retain the cache and framing work from that execution. -/
def vertexWithTerminalWork (κ : ℕ) (mode : ChargedVertexModes.Mode) (source tape : Bits) :
    Read (Σ n,PhysicalAmplifiedVertexSolver.Result n) × (ℕ × ℕ) :=
  vertexWithFramedRun runWithTerminalWork κ mode source tape

theorem vertexWithJoinedWork_reference (κ : ℕ) (mode : ChargedVertexModes.Mode) (source tape : Bits) :
    (vertexWithJoinedWork κ mode source tape).1=PaidFramedVertexWire.vertexWithCost κ mode source tape := by
  unfold vertexWithJoinedWork vertexWithFramedRun PaidFramedVertexWire.vertexWithCost
  dsimp only
  rw [PhysicalSourceInputJoin.vertex_framing_records_value]
  change _ = Read.bind (PhysicalSourceInputJoin.vertex source) _
  unfold Read.bind
  cases (PhysicalSourceInputJoin.vertex source).1 with
  | none => rfl
  | some encoded =>
    obtain ⟨n,D⟩ := encoded
    simp only [PaidFramedVertexWire.runWithCacheWork_reference]

theorem vertexWithJoinedWork_frames (κ : ℕ) (mode : ChargedVertexModes.Mode) (source tape : Bits) :
    (vertexWithJoinedWork κ mode source tape).2.2=(PhysicalSourceInputJoin.vertexWithFramingRecords source).2 := rfl

theorem vertex_joined_cache_polynomial : ∃ p : Polynomial ℕ,
    ∀ (κ : ℕ) (mode : ChargedVertexModes.Mode) (source tape : Bits),
      (vertexWithJoinedWork κ mode source tape).2.1 ≤ p.eval source.length := by
  obtain ⟨cache,paid⟩ := PhysicalSourceReadback.cache_polynomial
  refine ⟨cache.comp PaidFramedVertexWire.serializedLengthBound,?_⟩
  intro κ mode source tape
  unfold vertexWithJoinedWork vertexWithFramedRun
  dsimp only
  rw [PhysicalSourceInputJoin.vertex_framing_records_value,eval_comp]
  cases exactSource : (PhysicalSourceInputJoin.vertex source).1 with
  | none => exact Nat.zero_le _
  | some encoded =>
    obtain ⟨n,D⟩ := encoded
    change (PaidFramedVertexWire.runWithCacheWork κ mode D tape).2 ≤ _
    rw [PaidFramedVertexWire.run_cache_work]
    exact (paid D).trans (PhysicalIntegerRoundingCost.eval_mono cache (PaidFramedVertexWire.serialized_length_le exactSource))

theorem vertex_joined_polynomial : ∃ p : Polynomial ℕ,
    ∀ (κ : ℕ) (mode : ChargedVertexModes.Mode) (source tape : Bits),
      let r := vertexWithJoinedWork κ mode source tape
      r.1.2+r.2.1+r.2.2 ≤ p.eval (source.length+κ) := by
  obtain ⟨p, paid⟩ := PaidFramedVertexWire.wire_polynomial
  obtain ⟨c, cached⟩ := vertex_joined_cache_polynomial
  let framing := PhysicalSourceInputJoin.framingBudget (X : Polynomial ℕ)
  refine ⟨p+c+framing,?_⟩
  intro κ mode source tape
  have frame := ((PhysicalSourceInputJoin.framing_records_bound source).1.trans_eq
    (joined_framingBudget_eval source.length).symm).trans
      (PhysicalIntegerRoundingCost.eval_mono framing (Nat.le_add_right source.length κ))
  have cache := (cached κ mode source tape).trans
    (PhysicalIntegerRoundingCost.eval_mono c (Nat.le_add_right source.length κ))
  simp only [eval_add,vertexWithJoinedWork_reference,vertexWithJoinedWork_frames]
  exact Nat.add_le_add (Nat.add_le_add (paid κ mode source tape) cache) frame

def observeWireVertex (r : Σ n,PhysicalAmplifiedVertexSolver.Result n) :
    Σ n,EncodedVertexSolver.Output n × Bits := ⟨r.1,r.2.observe⟩

private def reachedTerminalWork (source : Bits) : ℕ :=
  ((PhysicalSourceInputJoin.vertex source).1.map fun ⟨_,D⟩ =>
    let raw := PhysicalSourceReadback.runWithTerminalCharge D
    ((raw.1.map (fun p => p.2.2)).getD 0)+raw.2).getD 0

private theorem vertex_terminal_comparison (κ : ℕ) (mode : ChargedVertexModes.Mode) (source tape : Bits) :
    let new := vertexWithTerminalWork κ mode source tape
    let old := vertexWithCost κ mode source tape
    new.1.1.map observeWireVertex=old.1.map observeWireVertex ∧
      new.1.2+new.2.1 ≤ old.2+reachedTerminalWork source := by
  unfold vertexWithTerminalWork vertexWithFramedRun vertexWithCost reachedTerminalWork
  dsimp only
  rw [PhysicalSourceInputJoin.vertex_framing_records_value]
  let earlier (encoded : Σ n,BinaryFractionalGuesses.Input n) :
      Read (Σ n,PhysicalAmplifiedVertexSolver.Result n) :=
    let r := run κ mode encoded.2 tape
    (r.1.map (fun out => ⟨encoded.1,out⟩),r.2)
  change _ = (Read.bind (PhysicalSourceInputJoin.vertex source) earlier).1.map observeWireVertex ∧
    _ ≤ (Read.bind (PhysicalSourceInputJoin.vertex source) earlier).2 + _
  unfold Read.bind
  cases found : (PhysicalSourceInputJoin.vertex source).1 with
  | none => exact ⟨rfl,by simp⟩
  | some encoded =>
    obtain ⟨n,D⟩ := encoded
    have h := runWithTerminalWork_comparison κ mode D tape
    let parsed := (PhysicalSourceInputJoin.vertex source).2
    let new := runWithTerminalWork κ mode D tape
    let old := run κ mode D tape
    change new.1.1.map PhysicalAmplifiedVertexSolver.Result.observe =
      old.1.map PhysicalAmplifiedVertexSolver.Result.observe ∧ _ at h
    constructor
    · have lifted := congrArg (Option.map (fun v : EncodedVertexSolver.Output n × Bits =>
        (⟨n,v⟩ : Σ i, EncodedVertexSolver.Output i × Bits))) h.1
      simpa only [earlier,Option.map_map,Function.comp_def,observeWireVertex] using lifted
    · simpa only [Option.map_some,Option.getD_some,Nat.add_assoc] using Nat.add_le_add_left h.2 parsed

theorem vertexWithTerminalWork_observe (κ : ℕ) (mode : ChargedVertexModes.Mode) (source tape : Bits) :
    (vertexWithTerminalWork κ mode source tape).1.1.map observeWireVertex =
      (vertexWithCost κ mode source tape).1.map observeWireVertex :=
  (vertex_terminal_comparison κ mode source tape).1

theorem vertex_terminal_polynomial : ∃ p : Polynomial ℕ,
    ∀ (κ : ℕ) (mode : ChargedVertexModes.Mode) (source tape : Bits),
      let r := vertexWithTerminalWork κ mode source tape
      r.1.2+r.2.1+r.2.2 ≤ p.eval (source.length+κ) := by
  obtain ⟨prior,paid⟩ := wire_polynomial
  obtain ⟨terminal,hterminal⟩ := PhysicalSourceReadback.terminal_charges_polynomial
  let framing := PhysicalSourceInputJoin.framingBudget (X : Polynomial ℕ)
  refine ⟨prior+terminal.comp serializedLengthBound+framing,?_⟩
  intro κ mode source tape
  let x := source.length+κ
  have lift : source.length ≤ x := Nat.le_add_right _ _
  have frame : (vertexWithTerminalWork κ mode source tape).2.2 ≤ framing.eval x :=
    ((PhysicalSourceInputJoin.framing_records_bound source).1.trans_eq
      (joined_framingBudget_eval source.length).symm).trans (eval_mono framing lift)
  have reader : reachedTerminalWork source ≤ terminal.eval (serializedLengthBound.eval x) := by
    unfold reachedTerminalWork
    cases sourceValue : (PhysicalSourceInputJoin.vertex source).1 with
    | none => exact Nat.zero_le _
    | some encoded =>
      obtain ⟨n,D⟩ := encoded
      exact (hterminal D).trans
        (eval_mono terminal ((serialized_length_le sourceValue).trans (eval_mono serializedLengthBound lift)))
  have compared := (vertex_terminal_comparison κ mode source tape).2
  change _ ≤ (prior+terminal.comp serializedLengthBound+framing).eval x
  rw [eval_add,eval_add,eval_comp]
  exact Nat.add_le_add (compared.trans (Nat.add_le_add (paid κ mode source tape) reader)) frame

def vertexWithTerminalScalarWork (κ : ℕ) (mode : ChargedVertexModes.Mode) (source tape : Bits) :
    Read (Σ n,PhysicalAmplifiedVertexSolver.Result n) × (ℕ × ℕ) :=
  vertexWithFramedRun runWithTerminalScalarWork κ mode source tape

theorem vertex_terminal_scalar_reference (κ : ℕ) (mode : ChargedVertexModes.Mode) (source tape : Bits) :
    let next := vertexWithTerminalScalarWork κ mode source tape
    let old := vertexWithTerminalWork κ mode source tape
    next.1=old.1 ∧ next.2.2=old.2.2 := by
  simp only [vertexWithTerminalScalarWork,vertexWithTerminalWork,vertexWithFramedRun]
  cases (PhysicalSourceInputJoin.vertexWithFramingRecords source).1.1 with
  | none => exact ⟨rfl,True.intro⟩
  | some encoded =>
    obtain ⟨n,D⟩ := encoded
    exact ⟨by simp only [run_terminal_scalar_reference],True.intro⟩

theorem vertex_terminal_scalar_polynomial : ∃ p : Polynomial ℕ,
    ∀ (κ : ℕ) (mode : ChargedVertexModes.Mode) (source tape : Bits),
      let r := vertexWithTerminalScalarWork κ mode source tape
      r.1.2+r.2.1+r.2.2 ≤ p.eval (source.length+κ) := by
  obtain ⟨p,paid⟩ := vertex_terminal_polynomial
  let width := p+4
  let calls : Polynomial ℕ := (X+2)*X+2
  let arithmetic := calls*PaidVertexAmplification.sampleControlBudget width+1
  refine ⟨p+arithmetic,fun κ mode source tape => ?_⟩
  let x := source.length+κ
  let old := vertexWithTerminalWork κ mode source tape
  let next := vertexWithTerminalScalarWork κ mode source tape
  have observed := vertex_terminal_scalar_reference κ mode source tape
  change next.1=old.1 ∧ next.2.2=old.2.2 at observed
  have all : old.1.2+old.2.1+old.2.2 ≤ p.eval x := paid κ mode source tape
  have extra : next.2.1 ≤ old.2.1+arithmetic.eval x := by
    unfold next old vertexWithTerminalScalarWork vertexWithTerminalWork vertexWithFramedRun
    dsimp only
    rw [PhysicalSourceInputJoin.vertex_framing_records_value]
    cases parsed : (PhysicalSourceInputJoin.vertex source).1 with
    | none => exact Nat.zero_le _
    | some encoded =>
      obtain ⟨n,D⟩ := encoded
      let sample := runWithTerminalWork κ mode D tape
      have included : sample.1.2 ≤ old.1.2 := by
        unfold old vertexWithTerminalWork vertexWithFramedRun
        dsimp only
        rw [PhysicalSourceInputJoin.vertex_framing_records_value,parsed]
        exact Nat.le_add_left _ _
      have maxPaid := included.trans ((Nat.le_add_right _ _).trans ((Nat.le_add_right _ _).trans all))
      have wide : (sample.1.2+4).size ≤ width.eval x := by
        simp only [width,eval_add,eval_ofNat]
        exact (BinaryNaturalOperations.size_le_self _).trans (Nat.add_le_add_right maxPaid 4)
      have stored : (ChargedSourceAssembly.vertex source).1=some ⟨n,D⟩ := by
        rwa [ChargedSourceAssembly.vertex_value,← PhysicalSourceInputJoin.vertex_value]
      have dim := (ChargedSourceAssembly.vertex_dimensions stored).1.trans (Nat.le_add_right source.length κ)
      have times : (BinarySolverOuterControls.vertex n κ).extra+2 ≤ calls.eval x := by
        rw [BinarySolverOuterControls.vertex_extra]
        simp only [calls,eval_add,eval_mul,eval_ofNat,eval_X]
        apply Nat.add_le_add_right
        exact (exponent_le n κ).trans (Nat.mul_le_mul (Nat.add_le_add_right dim 2) (Nat.le_add_left _ _))
      have bound := run_terminal_scalar_paid κ mode D tape wide
      change _ ≤ sample.2+arithmetic.eval x
      apply bound.trans
      simp only [arithmetic,eval_add,eval_mul,eval_one,PaidVertexAmplification.sampleControlBudget_eval]
      exact Nat.add_le_add_left (Nat.add_le_add_right (Nat.mul_le_mul_right _ times) 1) _
  change next.1.2+next.2.1+next.2.2 ≤ (p+arithmetic).eval x
  rw [observed.1,observed.2,eval_add]
  calc
    _ ≤ old.1.2+(old.2.1+arithmetic.eval x)+old.2.2 :=
      Nat.add_le_add_right (Nat.add_le_add_left extra _) _
    _ = old.1.2+old.2.1+old.2.2+arithmetic.eval x := by ac_rfl
    _ ≤ _ := Nat.add_le_add_right all _

def vertexWithTerminalSelectionWork (κ : ℕ) (mode : ChargedVertexModes.Mode) (source tape : Bits) :
    Read (Σ n,PhysicalAmplifiedVertexSolver.Result n) × (ℕ × ℕ) :=
  vertexWithFramedRun runWithTerminalSelectionWork κ mode source tape

theorem vertex_terminal_selection_reference (κ : ℕ) (mode : ChargedVertexModes.Mode) (source tape : Bits) :
    let new := vertexWithTerminalSelectionWork κ mode source tape
    let old := vertexWithTerminalScalarWork κ mode source tape
    new.1=old.1 ∧ new.2.2=old.2.2 := by
  simp only [vertexWithTerminalSelectionWork,vertexWithTerminalScalarWork,vertexWithFramedRun]
  cases (PhysicalSourceInputJoin.vertexWithFramingRecords source).1.1 with
  | none => exact ⟨rfl,True.intro⟩
  | some encoded =>
    obtain ⟨n,D⟩ := encoded
    exact ⟨by simp only [run_terminal_selection_reference],True.intro⟩

theorem vertex_terminal_selection_polynomial : ∃ p : Polynomial ℕ,
    ∀ (κ : ℕ) (mode : ChargedVertexModes.Mode) (source tape : Bits),
      let r := vertexWithTerminalSelectionWork κ mode source tape
      r.1.2+r.2.1+r.2.2 ≤ p.eval (source.length+κ) := by
  obtain ⟨paid,hPaid⟩ := vertex_terminal_scalar_polynomial
  let draws : Polynomial ℕ := (X+2)*X
  let selection := BinaryCutPriceSelection.minimumControlBudget draws
    (BinaryCutPriceSelection.fieldControlBudget X) paid
  refine ⟨paid+selection,fun κ mode source tape => ?_⟩
  let x := source.length+κ
  let old := vertexWithTerminalScalarWork κ mode source tape
  let new := vertexWithTerminalSelectionWork κ mode source tape
  have prior : old.1.2+old.2.1+old.2.2 ≤ paid.eval x := hPaid κ mode source tape
  have same := vertex_terminal_selection_reference κ mode source tape
  change new.1=old.1 ∧ new.2.2=old.2.2 at same
  have additional : new.2.1 ≤ old.2.1+selection.eval x := by
    unfold new old vertexWithTerminalSelectionWork vertexWithTerminalScalarWork vertexWithFramedRun
    dsimp only
    rw [PhysicalSourceInputJoin.vertex_framing_records_value]
    cases parsed : (PhysicalSourceInputJoin.vertex source).1 with
    | none => exact Nat.zero_le _
    | some encoded =>
      obtain ⟨n,D⟩ := encoded
      let run := runWithTerminalScalarWork κ mode D tape
      have initialFee : run.1.2 ≤ old.1.2 := by
        unfold old vertexWithTerminalScalarWork vertexWithFramedRun
        dsimp only
        rw [PhysicalSourceInputJoin.vertex_framing_records_value,parsed]
        exact Nat.le_add_left _ _
      have fee : run.1.2.size ≤ paid.eval x :=
        (BinaryNaturalOperations.size_le_self _).trans
          (initialFee.trans ((Nat.le_add_right _ _).trans ((Nat.le_add_right _ _).trans prior)))
      have stored : (ChargedSourceAssembly.vertex source).1=some ⟨n,D⟩ := by
        rwa [ChargedSourceAssembly.vertex_value,← PhysicalSourceInputJoin.vertex_value]
      have dim := (ChargedSourceAssembly.vertex_dimensions stored).1.trans (Nat.le_add_right source.length κ)
      have rounds : (BinarySolverOuterControls.vertex n κ).extra ≤ draws.eval x := by
        rw [BinarySolverOuterControls.vertex_extra]
        simp only [draws,eval_add,eval_mul,eval_X,eval_ofNat]
        exact (exponent_le n κ).trans (Nat.mul_le_mul (Nat.add_le_add_right dim 2) (Nat.le_add_left _ _))
      change _ ≤ run.2+selection.eval x
      apply (run_terminal_selection_paid κ mode D tape fee).trans
      simp only [selection,BinaryCutPriceSelection.minimumControlBudget_eval,
        BinaryCutPriceSelection.fieldControlBudget_eval,eval_X]
      exact Nat.add_le_add_left (BinaryCutPriceSelection.minimumControlBudget_mono rounds
        (BinaryCutPriceSelection.fieldControlBudget_mono dim) le_rfl) _
  change new.1.2+new.2.1+new.2.2 ≤ (paid+selection).eval x
  rw [same.1,same.2,eval_add]
  calc
    _ ≤ old.1.2+(old.2.1+selection.eval x)+old.2.2 :=
      Nat.add_le_add_right (Nat.add_le_add_left additional _) _
    _ = old.1.2+old.2.1+old.2.2+selection.eval x := by ac_rfl
    _ ≤ _ := Nat.add_le_add_right prior _

def vertexWithTerminalStreamWork (κ : ℕ) (mode : ChargedVertexModes.Mode) (source tape : Bits) :
    Read (Σ n,PhysicalAmplifiedVertexSolver.Result n) × (ℕ × ℕ) :=
  vertexWithFramedRun runWithTerminalStreamWork κ mode source tape

theorem vertex_terminal_stream_reference (κ : ℕ) (mode : ChargedVertexModes.Mode) (source tape : Bits) :
    let new := vertexWithTerminalStreamWork κ mode source tape
    let old := vertexWithTerminalSelectionWork κ mode source tape
    new.1=old.1 ∧ new.2.2=old.2.2 := by
  simp only [vertexWithTerminalStreamWork,vertexWithTerminalSelectionWork,vertexWithFramedRun]
  cases (PhysicalSourceInputJoin.vertexWithFramingRecords source).1.1 with
  | none => exact ⟨rfl,True.intro⟩
  | some encoded =>
    obtain ⟨n,D⟩ := encoded
    exact ⟨by simp only [run_terminal_stream_reference],True.intro⟩

theorem vertex_terminal_stream_polynomial : ∃ p : Polynomial ℕ,
    ∀ (κ : ℕ) (mode : ChargedVertexModes.Mode) (source tape : Bits),
      let r := vertexWithTerminalStreamWork κ mode source tape
      r.1.2+r.2.1+r.2.2 ≤ p.eval (source.length+κ) := by
  obtain ⟨paid,paidBound⟩ := vertex_terminal_selection_polynomial
  obtain ⟨phase,phaseBound⟩ := PhysicalAmplifiedBinaryVertex.vertex_wire_polynomial
  let draws : Polynomial ℕ := (X+2)*X+1
  let retained := draws*PaidVertexAmplification.retainedFeeBudget phase
  refine ⟨paid+retained,fun κ mode source tape => ?_⟩
  let x := source.length+κ
  let old := vertexWithTerminalSelectionWork κ mode source tape
  let new := vertexWithTerminalStreamWork κ mode source tape
  have prior : old.1.2+old.2.1+old.2.2 ≤ paid.eval x := paidBound κ mode source tape
  have same := vertex_terminal_stream_reference κ mode source tape
  change new.1=old.1 ∧ new.2.2=old.2.2 at same
  have additional : new.2.1≤old.2.1+retained.eval x := by
    unfold new old vertexWithTerminalStreamWork vertexWithTerminalSelectionWork vertexWithFramedRun
    dsimp only
    rw [PhysicalSourceInputJoin.vertex_framing_records_value]
    cases parsed : (PhysicalSourceInputJoin.vertex source).1 with
    | none => exact Nat.zero_le _
    | some encoded =>
      obtain ⟨n,D⟩ := encoded
      let earlier := runWithTerminalSelectionWork κ mode D tape
      have stored : (ChargedSourceAssembly.vertex source).1=some ⟨n,D⟩ := by
        rwa [ChargedSourceAssembly.vertex_value,← PhysicalSourceInputJoin.vertex_value]
      have width : ∀ out ∈ earlier.1.1, out.roundingAndSelection.size≤phase.eval x := by
        intro out present
        have phases := run_terminal_phase_reference κ mode D tape
        change earlier.1.1.map _=(PhysicalAmplifiedBinaryVertex.vertex κ mode D tape).map _ at phases
        rw [Option.mem_def.mp present,Option.map_some] at phases
        obtain ⟨spec,result,equal⟩ := Option.map_eq_some_iff.mp phases.symm
        have fromSource : (PhysicalAmplifiedBinaryVertex.vertexWithCost κ mode source tape).1=some ⟨n,spec⟩ := by
          simp only [PhysicalAmplifiedBinaryVertex.vertexWithCost,stored,PhysicalVertexSolver.prepareOn,
            Option.bind_some,result,Option.map_some]
        have bound := phaseBound κ mode source tape fromSource
        rw [← equal]
        exact (BinaryNaturalOperations.size_le_self _).trans ((Nat.le_add_left _ _).trans bound)
      have dim := (ChargedSourceAssembly.vertex_dimensions stored).1.trans (Nat.le_add_right source.length κ)
      have rounds : (BinarySolverOuterControls.vertex n κ).extra+1≤draws.eval x := by
        rw [BinarySolverOuterControls.vertex_extra]
        simp only [draws,eval_add,eval_mul,eval_X,eval_ofNat,eval_one]
        exact Nat.add_le_add_right ((exponent_le n κ).trans
          (Nat.mul_le_mul (Nat.add_le_add_right dim 2) (Nat.le_add_left _ _))) 1
      change _≤earlier.2+retained.eval x
      apply (run_terminal_stream_paid κ mode D tape width).trans
      simp only [retained,eval_mul,PaidVertexAmplification.retainedFeeBudget_eval]
      exact Nat.add_le_add_left (Nat.mul_le_mul_right _ rounds) _
  change new.1.2+new.2.1+new.2.2 ≤ (paid+retained).eval x
  rw [same.1,same.2,eval_add]
  calc
    _ ≤ old.1.2+(old.2.1+retained.eval x)+old.2.2 :=
      Nat.add_le_add_right (Nat.add_le_add_left additional _) _
    _ = old.1.2+old.2.1+old.2.2+retained.eval x := by ac_rfl
    _ ≤ _ := Nat.add_le_add_right prior _

end DirectedFlowCutGap.PaidFramedVertexWire
