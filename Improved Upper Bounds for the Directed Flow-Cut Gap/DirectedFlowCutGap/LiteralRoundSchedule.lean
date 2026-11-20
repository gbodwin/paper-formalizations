import DirectedFlowCutGap.PaidVertexAmplification

/-! Record the original input and starting tape at every attempted round,
including the last call when the tape is exhausted. -/
namespace DirectedFlowCutGap.LiteralRoundSchedule

open BinaryArithmetic BinaryFractionalRows EncodedVertexSolver
open FractionalCoverRawCore (RawRow)
open ChargedPhysicalVertexSolver (rowsCount)

structure Visit (n : ℕ) where
  input : RoundingInput n
  tape : Bits

def rows {n : ℕ} (D : BinaryFractionalGuesses.Input n) (costs : RawRow n)
    (round : PaidVertexSampling.Runner n) (T : ℕ) : List (RawRow n) → Bits → List (Visit n) × Option Bits
  | [],tape => ([],some tape)
  | head::tail,tape =>
      let input : RoundingInput n := ⟨D.adjacency,head,costs⟩
      let remaining := match (round T input tape).1 with
        | none => ([],none)
        | some out => rows D costs round T tail out.suffix
      (⟨input,tape⟩::remaining.1,remaining.2)

theorem rows_tape {n : ℕ} (D : BinaryFractionalGuesses.Input n) (costs : RawRow n)
    (round : PaidVertexSampling.Runner n) (T : ℕ) (plan : List (RawRow n)) (tape : Bits) :
    (rows D costs round T plan tape).2=(PaidVertexSampling.chooseRowsWith D costs round T plan tape).1.map Prod.snd := by
  simp only [PaidVertexSampling.chooseRows_value]
  induction plan generalizing tape with
  | nil => rfl
  | cons head tail ih =>
    simp only [rows,PhysicalVertexSampling.chooseRowsWith]
    cases h : (round T ⟨D.adjacency,head,costs⟩ tape).1 with
    | none => rfl
    | some out =>
      rw [ih]
      simp only [Option.bind_some,Option.map_map,Function.comp_def]

theorem rows_count {n : ℕ} (D : BinaryFractionalGuesses.Input n) (costs : RawRow n)
    (round : PaidVertexSampling.Runner n) (T : ℕ) (plan : List (RawRow n)) (tape : Bits) :
    (rows D costs round T plan tape).1.length ≤ plan.length := by
  induction plan generalizing tape with
  | nil => rfl
  | cons head tail ih =>
    simp only [rows,List.length_cons]
    cases h : (round T ⟨D.adjacency,head,costs⟩ tape).1 with
    | none => exact Nat.succ_le_succ (Nat.zero_le _)
    | some out => exact Nat.succ_le_succ (ih out.suffix)

def plan {n : ℕ} (D : BinaryFractionalGuesses.Input n) (costs : RawRow n)
    (round : PaidVertexSampling.Runner n) (T : ℕ) (cover : PhysicalCoverReader.Plan n) (tape : Bits) :
    List (Visit n) × Option Bits :=
  match cover with
  | .covers available => rows D costs round T available tape
  | .zero _ | .invalid | .infeasible _ => ([],some tape)

theorem plan_tape {n : ℕ} (D : BinaryFractionalGuesses.Input n) (costs : RawRow n)
    (round : PaidVertexSampling.Runner n) (T : ℕ) (cover : PhysicalCoverReader.Plan n) (tape : Bits) :
    (plan D costs round T cover tape).2=(PaidVertexSampling.fromPlanWith D costs round T cover tape).1.map Prod.snd := by
  cases cover with
  | invalid | infeasible _ | zero _ => rfl
  | covers available =>
    rw [plan,rows_tape]
    simp only [PaidVertexSampling.fromPlanWith,Option.map_map,Function.comp_def]

theorem plan_count {n : ℕ} (D : BinaryFractionalGuesses.Input n) (costs : RawRow n)
    (round : PaidVertexSampling.Runner n) (T : ℕ) (cover : PhysicalCoverReader.Plan n) (tape : Bits) :
    (plan D costs round T cover tape).1.length ≤ rowsCount cover := by
  cases cover with
  | invalid | infeasible _ | zero _ => exact le_rfl
  | covers available => exact rows_count D costs round T available tape

def samples {n : ℕ} (one : Bits → List (Visit n) × Option Bits) : ℕ → Bits → List (Visit n) × Option Bits
  | 0,tape => ([],some tape)
  | k+1,tape =>
    let tried := one tape
    match tried.2 with
    | none => tried
    | some rest =>
      let later := samples one k rest
      (tried.1++later.1,later.2)

theorem samples_count {n : ℕ} (one : Bits → List (Visit n) × Option Bits) (cap : ℕ)
    (fits : ∀ tape, (one tape).1.length ≤ cap) (k : ℕ) (tape : Bits) :
    (samples one k tape).1.length ≤ k*cap := by
  induction k generalizing tape with
  | zero => exact Nat.zero_le _
  | succ k ih =>
    simp only [samples,Nat.succ_mul]
    cases h : (one tape).2 with
    | none => exact (fits tape).trans (Nat.le_add_left _ _)
    | some rest =>
      simp only [List.length_append]
      exact (Nat.add_le_add (fits tape) (ih rest)).trans_eq (Nat.add_comm ..)

theorem samples_tape {A : Type} {n : ℕ} (one : Bits → List (Visit n) × Option Bits)
    (ref : Bits → PhysicalCoverAccess.Read ((A × ℕ) × Bits))
    (same : ∀ tape, (one tape).2=(ref tape).1.map Prod.snd) (k : ℕ) (tape : Bits) :
    (samples one k tape).2=(PaidVertexAmplification.samples ref k tape).1.map Prod.snd := by
  induction k generalizing tape with
  | zero => rfl
  | succ k ih =>
    simp only [samples,PaidVertexAmplification.samples,PhysicalCoverAccess.Read.bind_value,same]
    cases h : (ref tape).1 with
    | none => exact (same tape).trans (by rw [h]; rfl)
    | some values =>
      obtain ⟨value,rest⟩ := values
      simp only [Option.map_some,Option.bind_some,ih]
      cases (PaidVertexAmplification.samples ref k rest).1 <;> rfl

def amplified {n : ℕ} (D : BinaryFractionalGuesses.Input n) (round : PaidVertexSampling.Runner n)
    (draw extra confidence : ℕ) (cover : PhysicalCoverReader.Plan n) (tape : Bits) :
    List (Visit n) × Option Bits :=
  let setup := BinaryAmplificationPreparation.prepare D.costs draw extra confidence
  samples (plan D setup.costs round setup.trials cover) (extra+1) tape

theorem amplified_count {n : ℕ} (D : BinaryFractionalGuesses.Input n) (round : PaidVertexSampling.Runner n)
    (draw extra confidence : ℕ) (cover : PhysicalCoverReader.Plan n) (tape : Bits) :
    (amplified D round draw extra confidence cover tape).1.length ≤ (extra+1)*rowsCount cover := by
  let setup := BinaryAmplificationPreparation.prepare D.costs draw extra confidence
  exact samples_count (plan D setup.costs round setup.trials cover) (rowsCount cover)
    (plan_count D setup.costs round setup.trials cover) (extra+1) tape

theorem amplified_tape {n : ℕ} (D : BinaryFractionalGuesses.Input n) (round : PaidVertexSampling.Runner n)
    (draw extra confidence : ℕ) (cover : PhysicalCoverReader.Plan n) (dispatch readback : ℕ) (tape : Bits) :
    (amplified D round draw extra confidence cover tape).2 =
      (PaidVertexAmplification.runWithPlanRowWork D round draw extra confidence cover dispatch readback tape).1.1.map
        PhysicalAmplifiedVertexSolver.Result.suffix := by
  rw [PaidVertexAmplification.runWithPlanRowWork_reference,PaidVertexAmplification.runWithPlanStreamWork_reference,
    PaidVertexAmplification.runWithPlanSelectionWork_reference,PaidVertexAmplification.runWithPlanScalarWork_reference]
  let setup := BinaryAmplificationPreparation.prepare D.costs draw extra confidence
  let one := PaidVertexSampling.fromPlanWith D setup.costs round setup.trials cover
  have h := samples_tape (plan D setup.costs round setup.trials cover) one
    (plan_tape D setup.costs round setup.trials cover) (extra+1) tape
  change (amplified D round draw extra confidence cover tape).2= _ at h
  rw [h]
  simp only [PaidVertexAmplification.runWithPlan,PhysicalCoverAccess.Read.bind_value]
  cases (PaidVertexAmplification.samples one (extra+1) tape).1 with
  | none => rfl
  | some data =>
    obtain ⟨cuts,rest⟩ := data
    rfl

end DirectedFlowCutGap.LiteralRoundSchedule
