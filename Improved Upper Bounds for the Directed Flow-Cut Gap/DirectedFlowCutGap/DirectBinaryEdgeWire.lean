import DirectedFlowCutGap.PhysicalBinaryEdgeWire
import DirectedFlowCutGap.BinaryFractionalGuessesBounds

/-! Execute the charged binary fractional solver directly and feed the same
plan to the physical edge rounding and selection. -/
namespace DirectedFlowCutGap.DirectBinaryEdgeWire

open BinaryArithmetic EncodedEdgeLineInput
open PhysicalAmplifiedEdgeSolver (EdgeResult model)
open BinaryVertexReductionArithmetic (batch batch_value batch_paid)
open PhysicalCoverReader (Plan plan)
open FractionalCoverRawCore (RawRow)

private def rows {n : ℕ} {A : Type} (source : A → BinaryFractionalRows.Row n) :
    List A → List (RawRow n) × ℕ
  | [] => ([],2)
  | a::as =>
    let row := batch fun i => BinaryRawRational.decode (BinaryFractionalRows.get (source a) i)
    let more := rows source as
    (row.1::more.1,row.2+more.2+4)

private theorem rows_value {n : ℕ} {A : Type} (source : A → BinaryFractionalRows.Row n)
    (as : List A) :
    (rows source as).1=as.map (fun a => BinaryFractionalRows.decodeRow (source a)) := by
  induction as with
  | nil => rfl
  | cons a as ih =>
    simp only [rows,ih,List.map_cons,batch_value,BinaryRawRational.decode_value]
    congr

def read {n : ℕ} : BinaryFractionalGuesses.Output n → Plan n × ℕ
  | .infeasible d => (.infeasible d,2)
  | .zero mask => (.zero mask,2)
  | .covers found =>
    let decoded := rows (fun s => s.state.best) found
    (.covers decoded.1,decoded.2+4)
  | .invalid => (.invalid,2)

@[simp] theorem read_value {n : ℕ} (out : BinaryFractionalGuesses.Output n) :
    (read out).1=plan out := by
  cases out <;> simp only [read,plan,rows_value]

def rowBudget {R : Type*} [Semiring R] (n count width : R) : R :=
  count*(n*(40*(width+1)^2)+8*n+8)+6

private theorem rows_paid {n : ℕ} {A : Type} (source : A → BinaryFractionalRows.Row n)
    (as : List A) (width : ℕ)
    (fits : ∀ a ∈ as, ∀ i, BinaryRational.StoredBounded (BinaryFractionalRows.get (source a) i) width) :
    (rows source as).2 ≤ as.length*(n*(40*(width+1)^2)+8*n+8)+2 := by
  induction as with
  | nil => simp [rows]
  | cons a as ih =>
    have one := batch_paid (fun i => BinaryRawRational.decode (BinaryFractionalRows.get (source a) i))
      (fun i => BinaryRawRational.decode_paid (fits a (List.mem_cons_self ..) i))
    have tail := ih (fun r hr i => fits r (List.mem_cons_of_mem a hr) i)
    simp only [rows,List.length_cons,Nat.add_mul,Nat.one_mul]
    omega

theorem read_paid {n : ℕ} (out : BinaryFractionalGuesses.Output n) (count width : ℕ)
    (fits : match out with
      | .covers found => found.length≤count ∧
          ∀ row ∈ found, ∀ i, BinaryRational.StoredBounded (BinaryFractionalRows.get row.state.best i) width
      | _ => True) :
    (read out).2≤rowBudget n count width := by
  cases out with
  | infeasible d | zero d | invalid =>
    change 2 ≤ _*(n*(40*(width+1)^2)+8*n+8)+6
    omega
  | covers found =>
    have h := rows_paid (fun s => s.state.best) found width fits.2
    have hc := Nat.mul_le_mul_right (n*(40*(width+1)^2)+8*n+8) fits.1
    simp only [read,rowBudget]
    omega

theorem read_solveInput_paid {n : ℕ} (D : BinaryFractionalGuesses.Input n) :
    let cap := 1+PhysicalSourceDispatch.instructionPolynomial.eval (PhysicalSourceDispatch.input D).length
    (read (BinaryFractionalGuesses.solveInput D).1).2 ≤ rowBudget n cap cap :=
  read_paid _ _ _ (PhysicalCoverWidthEnvelope.solveInput_stored D)

def run {n : ℕ} (κ : ℕ) (D : Input n) (mode : ChargedVertexModes.Mode) (tape : Bits) : Option (EdgeResult n) :=
  let controls := BinarySolverOuterControls.edge n κ
  let input := PhysicalAmplifiedBinaryEdge.lineWithCost D
  let cover := BinaryFractionalGuesses.solveInput input.1
  let reader := read cover.1
  (PhysicalAmplifiedVertexSolver.runWithPlan input.1 (PhysicalAmplifiedBinaryEdge.round D mode)
    controls.draws controls.extra controls.confidence reader.1 cover.2 reader.2 tape).map
    (PhysicalAmplifiedBinaryEdge.finish D (input.2+controls.paid))

private def core {n : ℕ} (r : EdgeResult n) :
    (EncodedEdgeSolver.Output n × Bits) × ℕ := (r.observe,r.roundingAndSelection)

theorem run_core {n : ℕ} (κ : ℕ) (D : Input n) (mode : ChargedVertexModes.Mode) (tape : Bits) :
    (run κ D mode tape).map core=(PhysicalAmplifiedBinaryEdge.run κ D mode tape).map core := by
  obtain ⟨dispatch,readback,prior,_,_⟩ := PhysicalSourceReadback.run_eq (PhysicalAmplifiedBinaryEdge.lineWithCost D).1
  simp only [run,PhysicalAmplifiedBinaryEdge.run,PhysicalAmplifiedVertexSolver.run,prior,Option.bind_some,
    read_value,PhysicalAmplifiedVertexSolver.runWithPlan,Option.map_map,Function.comp_def,
    PhysicalAmplifiedBinaryEdge.finish,core,EdgeResult.observe]

theorem run_prefix_paid {n : ℕ} (κ : ℕ) (D : Input n) (mode : ChargedVertexModes.Mode) (tape : Bits)
    {r : EdgeResult n} (ran : run κ D mode tape=some r) :
    let line := (PhysicalAmplifiedBinaryEdge.lineWithCost D).1
    let cap := 1+PhysicalSourceDispatch.instructionPolynomial.eval (PhysicalSourceDispatch.input line).length
    r.dispatch ≤ BinaryFractionalGuessesBounds.solveInputBound (lineSize n) line.demands.length
      (BinaryFractionalGuessesBounds.scalarSize line.costs) ∧
    r.readback ≤ rowBudget (lineSize n) cap cap := by
  let line := (PhysicalAmplifiedBinaryEdge.lineWithCost D).1
  let cover := BinaryFractionalGuesses.solveInput line
  unfold run at ran
  obtain ⟨result,seen,rfl⟩ := Option.map_eq_some_iff.mp ran
  unfold PhysicalAmplifiedVertexSolver.runWithPlan at seen
  obtain ⟨⟨cuts,rest⟩,_,rfl⟩ := Option.map_eq_some_iff.mp seen
  change cover.2 ≤ _ ∧ (read cover.1).2 ≤ _
  exact ⟨BinaryFractionalGuessesBounds.solveInput_charge_from_data line,read_solveInput_paid line⟩

theorem run_rounding_polynomial : ∃ p : Polynomial ℕ,
    ∀ {n B : ℕ} (κ : ℕ) (D : Input n) (mode : ChargedVertexModes.Mode) (tape : Bits),
    1≤B →
    (∀ u v : Fin n, D.costs[u.val][v.val].num.size ≤ B ∧ D.costs[u.val][v.val].den.size ≤ B) →
    ∀ {r : EdgeResult n}, run κ D mode tape=some r →
      r.roundingAndSelection ≤ p.eval (n+D.demands.length+B+κ) := by
  obtain ⟨p,paid⟩ := PhysicalBinaryEdgeCost.edge_polynomial
  refine ⟨p,?_⟩
  intro n B κ D mode tape positive fits r ran
  have same := (run_core κ D mode tape).symm
  rw [ran,Option.map_some] at same
  obtain ⟨old,old_ran,eq⟩ := Option.map_eq_some_iff.mp same
  have amount : old.roundingAndSelection=r.roundingAndSelection := congrArg Prod.snd eq
  have bound := paid κ D mode tape positive fits old_ran
  omega

def runOn {n : ℕ} (κ : ℕ) (mode : ChargedVertexModes.Mode) (D : EncodedEdgeInput.Input n)
    (tape : Bits) : Option (EdgeResult n) :=
  let input := PhysicalBinaryEdgeWire.decodeWithCost D
  (run κ input.1 mode tape).map
    (fun r => { r with roundingAndSelection := r.roundingAndSelection+input.2 })

theorem runOn_core {n : ℕ} (κ : ℕ) (mode : ChargedVertexModes.Mode) (D : EncodedEdgeInput.Input n)
    (tape : Bits) : (runOn κ mode D tape).map core=(PhysicalBinaryEdgeWire.runOn κ mode D tape).map core := by
  have h := congrArg (Option.map (fun a : (EncodedEdgeSolver.Output n × Bits) × ℕ =>
    (a.1,a.2+(PhysicalBinaryEdgeWire.decodeWithCost D).2)))
    (run_core κ (PhysicalBinaryEdgeWire.decodeWithCost D).1 mode tape)
  simp only [runOn,PhysicalBinaryEdgeWire.runOn,Option.map_map,Function.comp_def,core,EdgeResult.observe] at h ⊢
  exact h

theorem runOn_observe {n : ℕ} (κ : ℕ) (mode : ChargedVertexModes.Mode) (D : EncodedEdgeInput.Input n)
    (tape : Bits) :
    (runOn κ mode D tape).map EdgeResult.observe =
      (EncodedSolverBits.run (EncodedEdgeSolver.bitTree κ (EncodedEdgeInput.decodeInput D) (model mode)) tape).map
        (fun (out,(rest,_)) => (out,rest)) := by
  have h := congrArg (Option.map Prod.fst) (runOn_core κ mode D tape)
  simp only [Option.map_map,Function.comp_def,core] at h
  exact h.trans (PhysicalBinaryEdgeWire.runOn_observe κ mode D tape)

def edgeWithCost (κ : ℕ) (mode : ChargedVertexModes.Mode) (source tape : Bits) :
    PhysicalCoverAccess.Read (Σ n,EdgeResult n) :=
  let parsed := ChargedSourceAssembly.edge source
  (PhysicalVertexSolver.prepareOn (fun _ input => runOn κ mode input tape) parsed.1,parsed.2)

def observeWire (r : Σ n,EdgeResult n) : Σ n,EncodedEdgeSolver.Output n × Bits :=
  ⟨r.1,r.2.observe⟩

attribute [local irreducible] runOn PhysicalBinaryEdgeWire.runOn ChargedSourceAssembly.edge

set_option maxHeartbeats 1000000 in
theorem wire_observe (κ : ℕ) (mode : ChargedVertexModes.Mode) (source tape : Bits) :
    (edgeWithCost κ mode source tape).1.map observeWire =
      (PhysicalBinaryEdgeWire.edgeWithCost κ mode source tape).1.map observeWire := by
  simp only [edgeWithCost,PhysicalBinaryEdgeWire.edgeWithCost,PhysicalVertexSolver.prepareOn]
  generalize (ChargedSourceAssembly.edge source).1 = parsed
  cases parsed with
  | none => simp only [Option.bind_none,Option.map_none]
  | some packed =>
    obtain ⟨n,D⟩ := packed
    simp only [Option.bind_some,Option.map_map,Function.comp_def]
    have h := congrArg (Option.map (fun a => (⟨n,a⟩ : Σ i,EncodedEdgeSolver.Output i × Bits)))
      ((runOn_observe κ mode D tape).trans (PhysicalBinaryEdgeWire.runOn_observe κ mode D tape).symm)
    simpa only [Option.map_map,Function.comp_def,observeWire] using h

theorem complete {n : ℕ} (κ : ℕ) (mode : ChargedVertexModes.Mode) (D : EncodedEdgeInput.Input n)
    (source tape : Bits) (parsed : EncodedEdgeInput.parse source=some ⟨n,D⟩)
    (enough : EncodedSolverBits.edgeBudget κ (EncodedEdgeInput.decodeInput D) ≤ tape.length) :
    ∃ r used, (edgeWithCost κ mode source tape).1=some ⟨n,r⟩ ∧ r.suffix=tape.drop used ∧
      used≤EncodedSolverBits.edgeBudget κ (EncodedEdgeInput.decodeInput D) ∧
        EncodedEdgeSolver.Valid (EncodedEdgeInput.decodeInput D) r.output := by
  obtain ⟨r,used,old,suffix,reads,valid⟩ := PhysicalBinaryEdgeWire.edge_complete κ mode D source tape parsed enough
  have same := wire_observe κ mode source tape
  rw [old,Option.map_some] at same
  obtain ⟨⟨m,out⟩,new,identity⟩ := Option.map_eq_some_iff.mp same
  change (⟨m,out.observe⟩ : Σ i,EncodedEdgeSolver.Output i × Bits)=⟨n,r.observe⟩ at identity
  obtain ⟨rfl,identity⟩ := Sigma.mk.inj_iff.mp identity
  have exact_pair : out.observe=r.observe := eq_of_heq identity
  refine ⟨out,used,new,(congrArg Prod.snd exact_pair).trans suffix,reads,?_⟩
  rw [show out.output=r.output from congrArg Prod.fst exact_pair]
  exact valid

end DirectedFlowCutGap.DirectBinaryEdgeWire
