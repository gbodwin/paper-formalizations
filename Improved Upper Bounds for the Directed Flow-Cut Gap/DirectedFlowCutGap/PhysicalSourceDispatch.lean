import DirectedFlowCutGap.PhysicalCoverExecution
import DirectedFlowCutGap.SourcePackingEncoding

/-!
# Source tables and fractional packing in one physical machine

The parser allocates its three input roots in the same heap used by the
dispatcher. One real register move installs the demand root for the
dispatcher. The source prefix and terminal attempt belong to that run.
-/

namespace DirectedFlowCutGap.PhysicalSourceDispatch

open BinaryArithmetic ImmutableReferenceSimulation ImmutableReferenceTerminal

def parseLabel (pc : Fin 64) : Fin 13384 := ⟨pc.val, by omega⟩
def solveLabel (pc : Fin 13320) : Fin 13384 := ⟨64 + pc.val, by omega⟩

def program : Program 13384 := fun pc =>
  if pc.val = 56 then .move .r2 .r3 (solveLabel 13318)
  else if hp : pc.val < 64 then
    ReferenceProgramLabels.instruction parseLabel (PackingSourceInput.program ⟨pc.val, hp⟩)
  else ReferenceProgramLabels.instruction solveLabel (FinalDispatch.program ⟨pc.val - 64, by omega⟩)

private theorem parse_slots (pc : Fin 64) (h : PackingSourceInput.program pc ≠ .halt) :
    program (parseLabel pc) =
      ReferenceProgramLabels.instruction parseLabel (PackingSourceInput.program pc) := by
  have hne : pc.val ≠ 56 := by
    intro he
    have hi : pc = 56 := Fin.ext he
    subst pc
    exact h rfl
  simp [program, parseLabel, hne, pc.isLt]

private theorem solve_slots (pc : Fin 13320) :
    program (solveLabel pc) =
      ReferenceProgramLabels.instruction solveLabel (FinalDispatch.program pc) := by
  have h1 : 64 + pc.val ≠ 56 := by omega
  have h2 : ¬64 + pc.val < 64 := by omega
  simp [program, solveLabel, h1, h2]

def input {n : ℕ} (D : BinaryFractionalGuesses.Input n) : Bits :=
  SourcePacking.encode D.costs D.adjacency D.demands

def initial (source : Bits) : BitState 13384 :=
  ⟨[], [], ⟨[], [], [], []⟩, [], parseLabel 48, source⟩

private def state (hp : NaturalHeap) (next a b c d : ℕ) (source : Bits) (pc : Fin 13384) :
    NaturalState 13384 :=
  ⟨hp, next, ⟨a, b, c, d⟩, [], pc, source⟩

def steps {n : ℕ} (D : BinaryFractionalGuesses.Input n) : ℕ :=
  PackingSourceInput.instructions (SourcePacking.capacityFields D.costs)
    (SourcePacking.matrixFields D.adjacency) (SourcePacking.demandFields D.demands) +
    1 + FinalDispatch.inputBound D.adjacency D.costs D.demands

private theorem append_run {C k j : ℕ} {p : Program C} {s u v : NaturalState C}
    {events suffix : List Event} (h : NaturalRun p k s events u) (hr : NaturalRun p j u suffix v) :
    NaturalRun p (k + j) s (events ++ suffix) v := by
  induction h with
  | done => simpa using hr
  | step h _ ih =>
    simpa [Nat.add_right_comm, List.append_assoc] using NaturalRun.step h (ih hr)

theorem high_trace {n : ℕ} (D : BinaryFractionalGuesses.Input n) :
    ∃ k out, k ≤ steps D ∧
      NaturalRun program k (eraseState (initial (input D))) ((input D).map Event.request) out ∧
      out.pc = solveLabel 13319 ∧ out.source = [] ∧
      FinalDispatch.Output out.heap out.registers.d (BinaryFractionalGuesses.solveInput D).1 := by
  let cap := SourcePacking.capacityFields D.costs
  let mat := SourcePacking.matrixFields D.adjacency
  let dem := SourcePacking.demandFields D.demands
  obtain ⟨heap, a, b, c, hp, hcap, hmat, hdem⟩ :=
    PackingSourceInput.prepare cap mat dem [] [] 0 0 0 0 0 rfl
  have ht : WordPairTableRead.Table heap a (IndexedRationalRead.fields D.costs.toList) := hcap
  have hm : GraphAdjacencyProgram.Matrix heap b (GraphRelaxationRefinement.matrix D.adjacency) := by
    simpa [mat, SourcePacking.matrixFields, List.map_map, Function.comp_def] using hmat
  obtain ⟨ds, hds, he⟩ := PackedOriginalStore.table_demands RowVertices.vertexLabel D.demands hdem
  obtain ⟨k, extra, root, hstep, hrun, hout⟩ :=
    FinalDispatch.compute (d := c) D.adjacency D.costs he ht hm hds heap.length rfl [] []
  have hparse : NaturalRun program (PackingSourceInput.instructions cap mat dem)
      (eraseState (initial (input D))) ((input D).map Event.request)
      (state heap heap.length a b b c [] (parseLabel 56)) := by
    have hp' := ReferenceProgramLabels.run parseLabel PackingSourceInput.program program parse_slots hp
    simpa [ReferenceProgramLabels.state, PackingSourceInput.state, state, initial,
      eraseState, State.map, Registers.map, input, SourcePacking.encode, cap, mat, dem, value] using hp'
  have hhandoff : tickNatural program (state heap heap.length a b b c [] (parseLabel 56)) =
      some ⟨state heap heap.length a b c c [] (solveLabel 13318), [], 0⟩ := by
    simp [tickNatural, program, parseLabel, state, Registers.get, Registers.set]
  let out := state (heap ++ extra) (heap.length + extra.length) a b c root [] (solveLabel 13319)
  have htail : NaturalRun program k (state heap heap.length a b c c [] (solveLabel 13318)) [] out := by
    have hr := ReferenceProgramLabels.run solveLabel FinalDispatch.program program (fun p _ => solve_slots p) hrun
    simpa [ReferenceProgramLabels.state, FinalDispatch.state, state, out] using hr
  have hl := hstep.trans (FinalDispatch.inputSteps_bound D.adjacency D.costs D.demands)
  have hh := append_run hparse (.step hhandoff htail)
  refine ⟨PackingSourceInput.instructions cap mat dem + 1 + k, out, ?_, ?_, rfl, rfl, ?_⟩
  · change PackingSourceInput.instructions cap mat dem + 1 + k ≤
      PackingSourceInput.instructions cap mat dem + 1 + FinalDispatch.inputBound D.adjacency D.costs D.demands
    omega
  · simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hh
  · exact hout

def paidBound {n : ℕ} (D : BinaryFractionalGuesses.Input n) : ℕ :=
  completeBound 13384 1 0 (steps D)

private theorem encodedTable_length (rows : List (Bits × Bits)) :
    (SourceRowTableProgram.encode rows).length =
      2 * SourceRowTableProgram.bits rows + 3 * rows.length + 1 := by
  induction rows with
  | nil => rfl
  | cons row rest ih =>
    rcases row with ⟨a, b⟩
    simp only [SourceRowTableProgram.encode, SourceRowTableProgram.bits, List.length_cons,
      List.length_append, SelfDelimitedWordProgram.encode_length, ih]
    omega

noncomputable def instructionPolynomial : Polynomial ℕ :=
  50 * Polynomial.X + 32 + FinalDispatchEnvelope.instructionPolynomial

theorem steps_polynomial {n : ℕ} (D : BinaryFractionalGuesses.Input n) :
    steps D ≤ instructionPolynomial.eval (input D).length := by
  let c := SourcePacking.capacityFields D.costs
  let m := SourcePacking.matrixFields D.adjacency
  let d := SourcePacking.demandFields D.demands
  let L := (input D).length
  have hc : c.length = n := by simp [c, SourcePacking.capacityFields, IndexedRationalRead.fields]
  have hm : m.length = n := by
    simpa [m, SourcePacking.matrixFields] using GraphRelaxationRefinement.matrix_length D.adjacency
  have hd : d.length = D.demands.length := by simp [d, SourcePacking.demandFields]
  have hbits : SourceRowTableProgram.bits c = LambdaRowProgram.rowBits D.costs.toList :=
    FinalDispatchEnvelope.fields_bits _
  have hL : L = 2 * (SourceRowTableProgram.bits c + SourceRowTableProgram.bits m +
      SourceRowTableProgram.bits d) + 3 * (c.length + m.length + d.length) + 3 := by
    change (PackingSourceInput.encode c m d).length = _
    simp only [PackingSourceInput.encode, List.length_append, encodedTable_length]
    omega
  have hd' : D.demands.length ≤ L := by omega
  have hn' : n ≤ L := by omega
  have hs : LambdaRowProgram.rowBits D.costs.toList ≤ L := by omega
  have hi := FinalDispatchEnvelope.instruction_le_eval D.adjacency D.costs D.demands hd' hn' hs
  change PackingSourceInput.instructions c m d + 1 + FinalDispatch.inputBound D.adjacency D.costs D.demands ≤
    instructionPolynomial.eval L
  simp only [PackingSourceInput.instructions, SourceRowTableProgram.steps, instructionPolynomial,
    Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_ofNat, Polynomial.eval_X]
  omega

noncomputable def paidPolynomial : Polynomial ℕ :=
  let t := instructionPolynomial
  let c := Polynomial.C (controlCost 13384 + 128)
  c * t * (2 * t + 2) ^ 2 + c * (t + 2) * (t + 1)

theorem paidBound_polynomial {n : ℕ} (D : BinaryFractionalGuesses.Input n) :
    paidBound D ≤ paidPolynomial.eval (input D).length := by
  have h := steps_polynomial D
  have he (B : ℕ) :
      paidPolynomial.eval B = completeBound 13384 1 0 (instructionPolynomial.eval B) := by
    simp [paidPolynomial, completeBound, runBound, stepBound]
    ring
  rw [he]
  unfold paidBound completeBound runBound stepBound
  gcongr

theorem bit_trace {n : ℕ} (D : BinaryFractionalGuesses.Input n) :
    ∃ k charge out, k ≤ steps D ∧
      Run program k charge (initial (input D)) ((input D).map Event.request) out ∧
      (attempt program out).result = none ∧ out.source = [] ∧
      charge + (attempt program out).operations ≤ paidBound D ∧
      FinalDispatch.Output (eraseState out).heap (eraseState out).registers.d
        (BinaryFractionalGuesses.solveInput D).1 := by
  obtain ⟨k, out, hk, hrun, hpc, hsource, hresult⟩ := high_trace D
  have hb : (initial (input D)).Bounded 1 0 := by
    simp [initial, State.Bounded, State.records, Registers.All, Heap.Bounded]
  have hhalt : tickNatural program out = none := by
    have h : program out.pc = .halt := by
      rw [hpc, solve_slots]
      rfl
    simp [tickNatural, h]
  obtain ⟨q, u, hu, he, hterm, hc, hs⟩ := terminating_simulation hb hrun hhalt
  refine ⟨k, q, u, hk, hu, hterm, hs.trans hsource, hc.trans ?_, ?_⟩
  · unfold paidBound completeBound runBound stepBound
    gcongr
  · rwa [he]

def runFrom {n : ℕ} (fuel : ℕ) (source : Bits) : Option (PhysicalCoverReader.Plan n × ℕ) := do
  let (out, charge) ← PhysicalCoverExecution.executeCached program fuel (initial source) 0
  let state := eraseState out
  let plan ← PhysicalCoverReader.readPlan n state.heap state.registers.d
  pure (plan, charge)

def run {n : ℕ} (D : BinaryFractionalGuesses.Input n) : Option (PhysicalCoverReader.Plan n × ℕ) :=
  runFrom (steps D + 1) (input D)

theorem run_eq {n : ℕ} (D : BinaryFractionalGuesses.Input n) :
    ∃ paid,
      run D = some (PhysicalCoverReader.plan (BinaryFractionalGuesses.solveInput D).1, paid) ∧
      paid ≤ paidBound D := by
  obtain ⟨k, charge, out, hk, hr, hh, _, hp, hout⟩ := bit_trace D
  have he := PhysicalCoverExecution.execute_eq hr hh (steps D + 1) 0 (by omega)
  refine ⟨charge + (attempt program out).operations, ?_, hp⟩
  simp [run, runFrom, PhysicalCoverExecution.executeCached_eq, he, PhysicalCoverReader.readPlan_eq hout]

end DirectedFlowCutGap.PhysicalSourceDispatch
