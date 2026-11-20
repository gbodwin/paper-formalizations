import DirectedFlowCutGap.FramedVertexStorage
import DirectedFlowCutGap.FramedVertexTrials
import DirectedFlowCutGap.RunnerCutoffStorage
import DirectedFlowCutGap.BinaryArrayNestedStorage

/-! Compose the original vertex source layout with the cutoff storage of each
reached attempt in the literal row and sample order. -/
namespace DirectedFlowCutGap.FramedVertexPackedLayout

open BinaryArithmetic EncodedArrayStorage Polynomial
open BinaryArrayNestedStorage (Code)
open CachedReferenceExecution (FastState)
open PhysicalSourceDispatch (initial program)
open PhysicalIntegerRoundingCost (eval_mono)
open PhysicalAmplifiedVertexSolver (Result)

def Prefix (source : Bits) (post : Code) : Prop :=
  match (PhysicalSourceInputJoin.vertex source).1 with
  | none => post=[]
  | some ⟨_,D⟩ =>
    let bits := (BinarySourceSerialization.run D).1
    let out := (PhysicalSourceBinaryCache.evaluate D bits (BinarySourceSerialization.run_value D)).1.1
    let plan := PhysicalCoverReader.plan (BinaryFractionalGuesses.solveInput D).1
    ∃ cache : Code, post=cache++BinaryCoverReadback.terminalArrayCode plan ∧
      (PhysicalSourceReadback.runWithBitCharges D).1.1=some plan ∧
      ∀ start : ℕ,
        let placed := allocateTrace (allocateTrace start (PhysicalSourceInputJoin.vertexArrayCode source)).1 cache
        PaidCacheTrace.Layout program (FastState.ofReference (initial bits))
          (allocateTrace start (PhysicalSourceInputJoin.vertexArrayCode source)).1 out placed.1 placed.2

def attempts {n : ℕ} (κ : ℕ) (mode : ChargedVertexModes.Mode) (D : BinaryFractionalGuesses.Input n)
    (cover : PhysicalCoverReader.Plan n) (tape : Bits) : List (LiteralRoundSchedule.Visit n) × Option Bits :=
  let controls := BinarySolverOuterControls.vertex n κ
  LiteralRoundSchedule.amplified D (PaidVertexRounding.runner mode) controls.draws controls.extra
    controls.confidence cover tape

def typedTape {n : ℕ} (κ : ℕ) (mode : ChargedVertexModes.Mode) (D : BinaryFractionalGuesses.Input n)
    (tape : Bits) : Option Bits :=
  match (PhysicalSourceReadback.runWithTerminalCharge D).1 with
  | none => none
  | some (cover,_,_) => (attempts κ mode D cover tape).2

set_option maxHeartbeats 1200000 in
private theorem typed_tape {n : ℕ} (κ : ℕ) (mode : ChargedVertexModes.Mode) (D : BinaryFractionalGuesses.Input n)
    (tape : Bits) : typedTape κ mode D tape =
      (PaidFramedVertexWire.runWithTerminalRowWork κ mode D tape).1.1.map Result.suffix := by
  let controls := BinarySolverOuterControls.vertex n κ
  let round := PaidVertexRounding.runner (n := n) mode
  let read := (PhysicalSourceReadback.runWithTerminalCharge D).1
  unfold typedTape PaidFramedVertexWire.runWithTerminalRowWork
  change (match read with | none => none | some (cover,_,_) => (attempts κ mode D cover tape).2) =
    ((match read with
    | none => ((none,controls.paid),(PhysicalSourceReadback.runWithTerminalCharge D).2)
    | some (cover,dispatch,reader) =>
      let r := PaidVertexAmplification.runWithPlanRowWork D round controls.draws controls.extra
        controls.confidence cover dispatch reader tape
      let out := r.1.1.map fun (out : Result n) =>
        { out with roundingAndSelection := out.roundingAndSelection+controls.paid }
      ((out,controls.paid+dispatch+reader+r.1.2),(PhysicalSourceReadback.runWithTerminalCharge D).2+r.2)) :
        PhysicalCoverAccess.Read (Result n) × ℕ).1.1.map Result.suffix
  cases read with
  | none => rfl
  | some data =>
    obtain ⟨cover,dispatch,reader⟩ := data
    simpa only [attempts,Option.map_map,Function.comp_def] using
      LiteralRoundSchedule.amplified_tape D round controls.draws controls.extra controls.confidence
        cover dispatch reader tape

def sourceTape (κ : ℕ) (mode : ChargedVertexModes.Mode) (source tape : Bits) : Option Bits :=
  match (PhysicalSourceInputJoin.vertex source).1 with
  | none => none
  | some ⟨_,D⟩ => typedTape κ mode D tape

theorem source_tape (κ : ℕ) (mode : ChargedVertexModes.Mode) (source tape : Bits) :
    sourceTape κ mode source tape = (PaidFramedVertexWire.vertexWithTerminalRowWork κ mode source tape).1.1.map
      (fun ⟨_,out⟩ => out.suffix) := by
  unfold sourceTape PaidFramedVertexWire.vertexWithTerminalRowWork
  let parsed := PhysicalSourceInputJoin.vertexWithFramingRecords source
  change (match (PhysicalSourceInputJoin.vertex source).1 with
    | none => none | some ⟨_,D⟩ => typedTape κ mode D tape) =
    ((match parsed.1.1 with
    | none => ((none,parsed.1.2),0)
    | some ⟨n,D⟩ =>
      let r := PaidFramedVertexWire.runWithTerminalRowWork κ mode D tape
      let out := r.1.1.map (fun out => (⟨n,out⟩ : Σ m,Result m))
      ((out,parsed.1.2+r.1.2),r.2)) : PhysicalCoverAccess.Read (Σ n,Result n) × ℕ).1.1.map
      (fun packed : Σ n,Result n => packed.2.suffix)
  dsimp only [parsed]
  rw [PhysicalSourceInputJoin.vertex_framing_records_value]
  cases (PhysicalSourceInputJoin.vertex source).1 with
  | none => rfl
  | some saved =>
    obtain ⟨n,D⟩ := saved
    simpa only [Option.map_map,Function.comp_def] using typed_tape κ mode D tape

def Model (κ : ℕ) (mode : ChargedVertexModes.Mode) (source tape : Bits) (code : Code) : Prop :=
  match (PhysicalSourceInputJoin.vertex source).1 with
  | none => code=[]
  | some ⟨n,D⟩ =>
    match (PhysicalSourceReadback.runWithTerminalCharge D).1 with
    | none => code=[]
    | some (cover,_,_) =>
      let controls := BinarySolverOuterControls.vertex n κ
      let ready := BinaryAmplificationPreparation.prepare D.costs controls.draws controls.extra controls.confidence
      ∃ parts : List Code, code=parts.flatten ∧ List.Forall₂
        (fun visit part => RunnerCutoffStorage.Model mode ready.trials visit.input visit.tape part)
        (attempts κ mode D cover tape).1 parts

private theorem assemble {A : Type} (p : A → Code → Prop) (visits : List A) (cells steps : ℕ)
    (fits : ∀ visit ∈ visits, ∃ part, p visit part ∧ fresh part ≤ cells ∧ part.length ≤ steps) :
    ∃ parts : List Code, List.Forall₂ p visits parts ∧ fresh parts.flatten ≤ visits.length*cells ∧
      parts.flatten.length ≤ visits.length*steps := by
  induction visits with
  | nil => exact ⟨[],.nil,Nat.zero_le _,Nat.zero_le _⟩
  | cons first rest ih =>
    obtain ⟨current,seen,space,work⟩ := fits first List.mem_cons_self
    obtain ⟨remaining,path,laterSpace,laterWork⟩ := ih (fun v hv => fits v (List.mem_cons_of_mem _ hv))
    refine ⟨current::remaining,.cons seen path,?_,?_⟩ <;>
      simp only [List.flatten_cons,List.length_cons,List.length_append,fresh_append,Nat.add_mul,Nat.one_mul] <;>
      omega

set_option maxHeartbeats 1900000 in
theorem polynomial : ∃ cells copies : Polynomial ℕ,
    ∀ (κ : ℕ) (mode : ChargedVertexModes.Mode) (source tape : Bits),
      let x := source.length+κ
      ∃ post rounds : Code, Prefix source post ∧ Model κ mode source tape rounds ∧
        let code := PhysicalSourceInputJoin.vertexArrayCode source++post++rounds
        fresh code ≤ cells.eval x ∧ code.length ≤ copies.eval x ∧
        ∀ start : ℕ,
          let placed := allocateTrace start code
          let width := (start+cells.eval x).size
          let binary := BinaryAllocationTrace.allocate start.bits (code.map BinaryAllocationTrace.reservation)
          (value binary.stop,binary.blocks.map (fun (a,b) => (value a,value b)))=placed ∧
            binary.charge ≤ BinaryAllocationTrace.chargeBound (copies.eval x) width ∧
            ∀ block∈placed.2, ∀ offset<block.2, (block.1+offset).size ≤ width := by
  obtain ⟨priorCells,priorCopies,prior⟩ := FramedVertexStorage.array_polynomial
  obtain ⟨trials,visits,counts⟩ := FramedVertexTrials.polynomial
  obtain ⟨roundCells,roundCopies,roundBound⟩ := RunnerCutoffStorage.arrays
  let pad := X+trials
  let laterCells := visits*roundCells.comp pad
  let laterCopies := visits*roundCopies.comp pad
  let cells := priorCells+laterCells
  let copies := priorCopies+laterCopies
  refine ⟨cells,copies,?_⟩
  intro κ mode source tape
  let x := source.length+κ
  obtain ⟨post,priorModel,priorSpace,priorWork,_⟩ := prior source
  let before := PhysicalSourceInputJoin.vertexArrayCode source++post
  have prefixSpace : fresh before ≤ priorCells.eval x := priorSpace.trans (eval_mono _ (Nat.le_add_right _ _))
  have prefixWork : before.length ≤ priorCopies.eval x := priorWork.trans (eval_mono _ (Nat.le_add_right _ _))
  have suffix : ∃ rounds : Code, Model κ mode source tape rounds ∧ fresh rounds ≤ laterCells.eval x ∧
      rounds.length ≤ laterCopies.eval x := by
    unfold Model
    cases parsed : (PhysicalSourceInputJoin.vertex source).1 with
    | none => exact ⟨[],rfl,Nat.zero_le _,Nat.zero_le _⟩
    | some saved =>
      obtain ⟨n,D⟩ := saved
      let cover := PhysicalCoverReader.plan (BinaryFractionalGuesses.solveInput D).1
      let controls := BinarySolverOuterControls.vertex n κ
      let ready := BinaryAmplificationPreparation.prepare D.costs controls.draws controls.extra controls.confidence
      let walk := attempts κ mode D cover tape
      obtain ⟨dispatch,_,reader,_,read,_⟩ := PhysicalSourceReadback.terminal_headers D
      obtain ⟨trialBound,visitBound⟩ := counts parsed κ mode tape
      have original : (ChargedSourceAssembly.vertex source).1=some ⟨n,D⟩ := by
        simpa only [ChargedSourceAssembly.vertex_value,← PhysicalSourceInputJoin.vertex_value] using parsed
      have nBound := (ChargedSourceAssembly.vertex_dimensions original).1.trans (Nat.le_add_right _ κ)
      have padded : n+ready.trials ≤ pad.eval x := by
        simp only [pad,eval_add,eval_X]
        exact Nat.add_le_add nBound trialBound
      let model (v : LiteralRoundSchedule.Visit n) (code : Code) :=
        RunnerCutoffStorage.Model mode ready.trials v.input v.tape code
      have each (v : LiteralRoundSchedule.Visit n) : ∃ code, model v code ∧
          fresh code ≤ roundCells.eval (pad.eval x) ∧ code.length ≤ roundCopies.eval (pad.eval x) := by
        obtain ⟨code,seen,space,work⟩ := roundBound mode ready.trials v.input v.tape
        exact ⟨code,seen,space.trans (eval_mono _ padded),work.trans (eval_mono _ padded)⟩
      obtain ⟨parts,path,space,work⟩ := assemble model walk.1 (roundCells.eval (pad.eval x))
        (roundCopies.eval (pad.eval x)) (fun v _ => each v)
      refine ⟨parts.flatten,?_,?_,?_⟩
      · simp only [read]
        exact ⟨parts,rfl,path⟩
      · simp only [laterCells,eval_mul,eval_comp]
        exact space.trans (Nat.mul_le_mul_right _ visitBound)
      · simp only [laterCopies,eval_mul,eval_comp]
        exact work.trans (Nat.mul_le_mul_right _ visitBound)
  obtain ⟨rounds,modeled,afterSpace,afterWork⟩ := suffix
  let code := before++rounds
  have space : fresh code ≤ cells.eval x := by
    simpa only [code,fresh_append,cells,eval_add] using Nat.add_le_add prefixSpace afterSpace
  have work : code.length ≤ copies.eval x := by
    simpa only [code,List.length_append,copies,eval_add] using Nat.add_le_add prefixWork afterWork
  refine ⟨post,rounds,priorModel,modeled,space,work,fun start => ?_⟩
  obtain ⟨same,paid,widths⟩ := PackedArrayReservations.binary_layout code start
  have width : (start+fresh code).size ≤ (start+cells.eval x).size := Nat.size_le_size (Nat.add_le_add_left space start)
  exact ⟨same,paid.trans (by unfold BinaryAllocationTrace.chargeBound; gcongr),
    fun block mem offset fits => (widths block mem offset fits).trans width⟩

end DirectedFlowCutGap.FramedVertexPackedLayout
