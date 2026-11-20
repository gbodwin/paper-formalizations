import DirectedFlowCutGap.PaidVertexSampling
/-! Accumulate the work of every attempted sample on the literal tape. -/
namespace DirectedFlowCutGap.PaidVertexAmplification

open BinaryArithmetic BinaryFractionalRows BinaryRational
open EncodedVertexSolver (Output)
open PhysicalCoverAccess (Read)
open PhysicalAmplifiedVertexSolver (Result)

def samples {A : Type} (one : Bits → Read ((A × ℕ) × Bits)) :
    (k : ℕ) → Bits → Read ((Fin k → A × ℕ) × Bits)
  | 0,tape => (some (Fin.elim0,tape),1)
  | k+1,tape =>
      let r : Read ((Fin (k+1) → A × ℕ) × Bits) := do
        let (first,rest) ← one tape
        let (later,suffix) ← samples one k rest
        pure (Fin.cons first later,suffix)
      (r.1,r.2+4)

theorem samples_value {A : Type} (one : Bits → Read ((A × ℕ) × Bits)) (k : ℕ) (tape : Bits) :
    (samples one k tape).1=PhysicalAmplifiedVertexSolver.samples (fun bits => (one bits).1) k tape := by
  induction k generalizing tape with
  | zero => rfl
  | succ k ih =>
      simp only [samples,PhysicalAmplifiedVertexSolver.samples, Read.bind_value]
      cases first : (one tape).1 with
      | none => rfl
      | some r =>
          rcases r with ⟨out,rest⟩
          simp only [Option.bind_some,← ih]
          cases (samples one k rest).1 <;> rfl

theorem samples_paid {A : Type} (one : Bits → Read ((A × ℕ) × Bits)) (budget k : ℕ)
    (paid : ∀ bits, (one bits).2 ≤ budget) (tape : Bits) :
    (samples one k tape).2 ≤ k*(budget+4)+1 := by
  induction k generalizing tape with
  | zero => simp [samples]
  | succ k ih =>
      let r : Read ((Fin (k+1) → A × ℕ) × Bits) := do
        let (first,rest) ← one tape
        let (later,suffix) ← samples one k rest
        pure (Fin.cons first later,suffix)
      have b : r.2 ≤ budget+(k*(budget+4)+1) := by
        apply Read.bind_bound (paid tape)
        rintro ⟨first,rest⟩ _
        refine (Read.bind_bound (r:=samples one k rest) (later:=0) (ih rest) ?_).trans_eq (Nat.add_zero _)
        rintro ⟨later,suffix⟩ _
        exact Nat.le_refl 0
      change r.2+4 ≤ _
      rw [Nat.succ_mul]
      omega

private def finish {n : ℕ} (costs : Row n) (extra setup dispatch readback : ℕ)
    (cuts : Fin (extra+1) → Output n × ℕ) (rest : Bits) : Read (Result n) :=
  let winner := BinaryCutPriceSelection.minimum (BinaryCutPriceSelection.cutScore costs) extra (fun i => (cuts i).1)
  let paid := (List.ofFn fun i => (cuts i).2).sum
  let copy := 20*(extra+1)^2+5
  (some ⟨winner.value,rest,dispatch,readback,paid+winner.charge+20*(extra+1)^2+5+setup⟩,winner.charge+copy)

private theorem finish_value {n : ℕ} (costs : Row n) (extra setup dispatch readback : ℕ)
    (cuts : Fin (extra+1) → Output n × ℕ) (rest : Bits) :
    (finish costs extra setup dispatch readback cuts rest).1 =
      some ⟨(ChargedAmplification.select costs extra cuts).1,rest,dispatch,readback,
        (ChargedAmplification.select costs extra cuts).2+setup⟩ := rfl

private theorem finish_paid {n B : ℕ} (costs : Row n) (extra setup dispatch readback : ℕ)
    (cuts : Fin (extra+1) → Output n × ℕ) (rest : Bits)
    (positive : 1 ≤ B) (fits : ∀ i, StoredBounded (get costs i) B) :
    (finish costs extra setup dispatch readback cuts rest).2 ≤
      BinaryCutPriceSelection.selectionBound extra n B+(20*(extra+1)^2+5) := by
  have limit := (BinaryCutPriceSelection.minimum_charge
    (BinaryCutPriceSelection.cutScore costs) extra (fun i => (cuts i).1) (n*(B+1)+1) (sumBound n B)
    (fun i => BinaryCutPriceSelection.cutScore_charge costs (cuts i).1 positive fits)).2
  exact Nat.add_le_add_right limit _

def runWithPlan {n : ℕ} (D : BinaryFractionalGuesses.Input n) (round : PaidVertexSampling.Runner n)
    (roundBound extra confidence : ℕ) (plan : PhysicalCoverReader.Plan n)
    (dispatch readback : ℕ) (tape : Bits) : Read (Result n) :=
  let setup := BinaryAmplificationPreparation.prepare D.costs roundBound extra confidence
  let all := samples (PaidVertexSampling.fromPlanWith D setup.costs round setup.trials plan) (extra+1) tape
  let selected := all >>= fun (cuts,rest) => finish D.costs extra setup.paid dispatch readback cuts rest
  (selected.1,setup.paid+selected.2)

theorem runWithPlan_value {n : ℕ} (D : BinaryFractionalGuesses.Input n) (round : PaidVertexSampling.Runner n)
    (roundBound extra confidence : ℕ) (plan : PhysicalCoverReader.Plan n) (dispatch readback : ℕ) (tape : Bits) :
    (runWithPlan D round roundBound extra confidence plan dispatch readback tape).1 =
      PhysicalAmplifiedVertexSolver.runWithPlan D (fun T input tape => (round T input tape).1)
        roundBound extra confidence plan dispatch readback tape := by
  simp only [runWithPlan,PhysicalAmplifiedVertexSolver.runWithPlan,Read.bind_value,samples_value,
    PaidVertexSampling.fromPlan_value]
  let setup := BinaryAmplificationPreparation.prepare D.costs roundBound extra confidence
  let one := PhysicalVertexSampling.fromPlanWith D setup.costs (fun T input tape => (round T input tape).1)
    setup.trials plan
  cases PhysicalAmplifiedVertexSolver.samples one (extra+1) tape with
  | none => rfl
  | some answer =>
      rcases answer with ⟨cuts,rest⟩
      exact finish_value _ _ _ _ _ _ _

theorem runWithPlan_paid {n B : ℕ} (D : BinaryFractionalGuesses.Input n) (round : PaidVertexSampling.Runner n)
    (roundBound extra confidence : ℕ) (plan : PhysicalCoverReader.Plan n) (dispatch readback sampleBudget : ℕ)
    (positive : 1 ≤ B) (fits : ∀ i, StoredBounded (get D.costs i) B) (tape : Bits)
    (each : let setup := BinaryAmplificationPreparation.prepare D.costs roundBound extra confidence
      ∀ bits, (PaidVertexSampling.fromPlanWith D setup.costs round setup.trials plan bits).2 ≤ sampleBudget) :
    (runWithPlan D round roundBound extra confidence plan dispatch readback tape).2 ≤
      BinaryAmplificationPreparation.budget (n+B+roundBound+extra+confidence)+
        ((extra+1)*(sampleBudget+4)+1+(BinaryCutPriceSelection.selectionBound extra n B+(20*(extra+1)^2+5))) := by
  have setup := BinaryAmplificationPreparation.prepare_paid D.costs roundBound extra confidence fits
    (x := n+B+roundBound+extra+confidence) (by omega) (by omega) (by omega) (by omega) (by omega)
  unfold runWithPlan
  apply Nat.add_le_add setup
  apply Read.bind_bound (samples_paid _ sampleBudget (extra+1) each tape)
  rintro ⟨cuts,rest⟩ _
  exact finish_paid _ _ _ _ _ cuts rest positive fits

theorem samples_extra {A : Type} (old newer : Bits → Read ((A × ℕ) × Bits)) (cap k : ℕ) (tape : Bits)
    (same : ∀ bits, (newer bits).1=(old bits).1) (paid : ∀ bits, (newer bits).2 ≤ (old bits).2+cap) :
    (samples newer k tape).2 ≤ (samples old k tape).2+k*cap := by
  have sameSample : (fun bits => (newer bits).1)=(fun bits => (old bits).1) := funext same
  induction k generalizing tape with
  | zero => simp [samples]
  | succ k ih =>
      let rest (one : Bits → Read ((A × ℕ) × Bits)) (first : (A × ℕ) × Bits) :
          Read ((Fin (k+1) → A × ℕ) × Bits) := do
        let (later,suffix) ← samples one k first.2
        pure (Fin.cons first.1 later,suffix)
      have tail (first : (A × ℕ) × Bits) : (rest newer first).2 ≤ (rest old first).2+k*cap := by
        have result : (samples newer k first.2).1=(samples old k first.2).1 := by
          simp only [samples_value,sameSample]
        let keep (answer : (Fin k → A × ℕ) × Bits) : Read ((Fin (k+1) → A × ℕ) × Bits) :=
          pure (Fin.cons first.1 answer.1,answer.2)
        have h := PaidVertexSampling.bind_extra (e := 0) result (ih first.2)
          (f := keep) (g := keep) (fun _ _ => Nat.le_add_right _ _)
        exact h.trans_eq (Nat.add_zero _)
      have billed := PaidVertexSampling.bind_extra (same tape) (paid tape) (fun first _ => tail first)
      unfold samples
      simp only [Nat.succ_mul]
      change (newer tape >>= rest newer).2+4 ≤ (old tape >>= rest old).2+4+(k*cap+cap)
      omega

theorem runWithPlan_extra_on_rows {n : ℕ} (D : BinaryFractionalGuesses.Input n) (old newer : PaidVertexSampling.Runner n)
    (roundBound extra confidence : ℕ) (plan : PhysicalCoverReader.Plan n) (dispatch readback cap : ℕ) (tape : Bits)
    (same : ∀ T input bits, (newer T input bits).1=(old T input bits).1)
    (paid : let setup := BinaryAmplificationPreparation.prepare D.costs roundBound extra confidence
      ∀ rows, plan=.covers rows → ∀ y ∈ rows, ∀ bits,
        (newer setup.trials ⟨D.adjacency,y,setup.costs⟩ bits).2 ≤
          (old setup.trials ⟨D.adjacency,y,setup.costs⟩ bits).2+cap) :
    (runWithPlan D newer roundBound extra confidence plan dispatch readback tape).2 ≤
      (runWithPlan D old roundBound extra confidence plan dispatch readback tape).2+
        (extra+1)*(ChargedPhysicalVertexSolver.rowsCount plan*cap) := by
  let setup := BinaryAmplificationPreparation.prepare D.costs roundBound extra confidence
  let sample (round : PaidVertexSampling.Runner n) := PaidVertexSampling.fromPlanWith D setup.costs round setup.trials plan
  have sameRound : (fun t input bits => (newer t input bits).1)=(fun t input bits => (old t input bits).1) :=
    funext fun t => funext fun i => funext fun bits => same t i bits
  have sameOne (bits : Bits) : (sample newer bits).1=(sample old bits).1 := by
    simp only [sample,PaidVertexSampling.fromPlan_value,sameRound]
  have sampleSame : (fun bits => (sample newer bits).1)=(fun bits => (sample old bits).1) := funext sameOne
  have added (bits : Bits) : (sample newer bits).2 ≤
      (sample old bits).2+ChargedPhysicalVertexSolver.rowsCount plan*cap :=
    PaidVertexSampling.fromPlan_extra_on_rows D setup.costs old newer setup.trials cap plan bits same paid
  let oldAll := samples (sample old) (extra+1) tape
  let newAll := samples (sample newer) (extra+1) tape
  have identical : newAll.1=oldAll.1 := by
    simp only [newAll,oldAll,samples_value,sampleSame]
  have fee := samples_extra (sample old) (sample newer) _ (extra+1) tape sameOne added
  let finishRun : ((Fin (extra+1) → Output n × ℕ) × Bits) → Read (Result n) :=
    fun (cuts,rest) => finish D.costs extra setup.paid dispatch readback cuts rest
  have total := PaidVertexSampling.bind_extra (e := 0) (f := finishRun) (g := finishRun)
    identical fee (fun _ _ => Nat.le_add_right _ _)
  change setup.paid+(newAll >>= finishRun).2 ≤ setup.paid+(oldAll >>= finishRun).2+
    (extra+1)*(ChargedPhysicalVertexSolver.rowsCount plan*cap)
  simp only [Nat.add_zero] at total
  omega

theorem runWithPlan_extra {n : ℕ} (D : BinaryFractionalGuesses.Input n) (old newer : PaidVertexSampling.Runner n)
    (roundBound extra confidence : ℕ) (plan : PhysicalCoverReader.Plan n) (dispatch readback cap : ℕ) (tape : Bits)
    (same : ∀ T input bits, (newer T input bits).1=(old T input bits).1)
    (paid : ∀ T input bits, (newer T input bits).2 ≤ (old T input bits).2+cap) :
    (runWithPlan D newer roundBound extra confidence plan dispatch readback tape).2 ≤
      (runWithPlan D old roundBound extra confidence plan dispatch readback tape).2+
        (extra+1)*(ChargedPhysicalVertexSolver.rowsCount plan*cap) :=
  runWithPlan_extra_on_rows D old newer roundBound extra confidence plan dispatch readback cap tape same
    (fun _ _ _ _ bits => paid _ _ bits)

/-- Dispatch and readback headers are stored in the result. They do not
change the selected cut, unread tape, or work of the amplification stage. -/
theorem runWithPlan_headers {n : ℕ} (D : BinaryFractionalGuesses.Input n) (round : PaidVertexSampling.Runner n)
    (roundBound extra confidence : ℕ) (plan : PhysicalCoverReader.Plan n) (d r d' r' : ℕ) (tape : Bits) :
    let before := runWithPlan D round roundBound extra confidence plan d r tape
    let after := runWithPlan D round roundBound extra confidence plan d' r' tape
    (after.1.map Result.observe,after.2)=(before.1.map Result.observe,before.2) := by
  let setup := BinaryAmplificationPreparation.prepare D.costs roundBound extra confidence
  let all := samples (PaidVertexSampling.fromPlanWith D setup.costs round setup.trials plan) (extra+1) tape
  unfold runWithPlan
  dsimp only
  change (((all >>= fun (cuts,rest) => finish D.costs extra setup.paid d' r' cuts rest).1.map Result.observe),
      setup.paid+(all >>= fun (cuts,rest) => finish D.costs extra setup.paid d' r' cuts rest).2) =
    (((all >>= fun (cuts,rest) => finish D.costs extra setup.paid d r cuts rest).1.map Result.observe),
      setup.paid+(all >>= fun (cuts,rest) => finish D.costs extra setup.paid d r cuts rest).2)
  change (((Read.bind all _).1.map Result.observe),setup.paid+(Read.bind all _).2) =
    (((Read.bind all _).1.map Result.observe),setup.paid+(Read.bind all _).2)
  unfold Read.bind
  cases all.1 with
  | none => rfl
  | some data =>
    rcases data with ⟨cuts,rest⟩
    rfl

end DirectedFlowCutGap.PaidVertexAmplification
