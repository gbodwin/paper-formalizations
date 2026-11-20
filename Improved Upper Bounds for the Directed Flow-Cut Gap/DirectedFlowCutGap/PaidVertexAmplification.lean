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

/-- Charge the binary sums of earlier sample work while walking one literal
tape. When a sample fails, its spent work is kept and later samples are skipped. -/
def samplesWithCharges {A : Type} (one : Bits → Read ((A × ℕ) × Bits)) :
    (k : ℕ) → Bits → Read ((Fin k → A × ℕ) × Bits) × ℕ
  | 0,tape => ((some (Fin.elim0,tape),1),1)
  | k+1,tape =>
    let head := one tape
    match head.1 with
    | none =>
      let fee := BinaryNaturalOperations.add head.2 4
      ((none,fee.1),fee.2+4)
    | some (first,rest) =>
      let tail := samplesWithCharges one k rest
      let prior := BinaryNaturalOperations.add head.2 tail.1.2
      let fee := BinaryNaturalOperations.add prior.1 4
      ((tail.1.1.map (fun (later,suffix) => (Fin.cons first later,suffix)),fee.1),
        tail.2+prior.2+fee.2+8)

private theorem bind_charge {A B : Type} (r : Read A) (k : A → Read B) :
    (r >>= k).2=r.2+(r.1.map fun a => (k a).2).getD 0 := by
  change (Read.bind r k).2=_
  unfold Read.bind
  cases r.1 <;> simp

theorem samplesWithCharges_reference {A : Type} (one : Bits → Read ((A × ℕ) × Bits))
    (k : ℕ) (tape : Bits) : (samplesWithCharges one k tape).1=samples one k tape := by
  induction k generalizing tape with
  | zero => rfl
  | succ k ih =>
    simp only [samplesWithCharges,samples,Read.bind_value,bind_charge]
    cases h : (one tape).1 with
    | none => simp only [Option.bind_none,Option.map_none,Option.getD_none,Nat.add_zero,
        BinaryNaturalOperations.add_value]
    | some item =>
      obtain ⟨first,rest⟩ := item
      simp only [Option.bind_some,Option.map_some,Option.getD_some,ih rest,
        BinaryNaturalOperations.add_value]
      cases (samples one k rest).1 with
      | none => simp only [Option.map_none,Option.bind_none,Option.getD_none,Nat.add_zero]
      | some item =>
        obtain ⟨later,suffix⟩ := item
        simp only [Option.map_some,Option.bind_some,Option.getD_some,Read.pure_value,Read.pure_charge,
          Nat.add_zero]

def sampleControlBudget {R : Type*} [Semiring R] (B : R) : R := 2*(BinaryRawRational.budget B+4)+8

open Polynomial in
theorem sampleControlBudget_eval (B : Polynomial ℕ) (x : ℕ) :
    (sampleControlBudget B).eval x=sampleControlBudget (B.eval x) := by
  simp only [sampleControlBudget,BinaryRawRational.budget,eval_add,eval_mul,eval_pow,eval_ofNat]

private theorem samples_step_fee {A : Type} (one : Bits → Read ((A × ℕ) × Bits)) (k : ℕ) (tape : Bits) :
    (samples one (k+1) tape).2 =
      (one tape).2+((one tape).1.map fun out => (samples one k out.2).2).getD 0+4 := by
  simp only [samples,bind_charge]
  cases h : (one tape).1 with
  | none => rfl
  | some answer =>
    obtain ⟨first,rest⟩ := answer
    simp only [Option.map_some,Option.getD_some]
    cases (samples one k rest).1 <;> simp

theorem samplesWithCharges_paid {A : Type} (one : Bits → Read ((A × ℕ) × Bits))
    (k : ℕ) {B : ℕ} (tape : Bits) (width : ((samples one k tape).2+4).size ≤ B) :
    (samplesWithCharges one k tape).2 ≤ k*sampleControlBudget B+1 := by
  induction k generalizing tape with
  | zero => simp only [samplesWithCharges,Nat.zero_mul,Nat.zero_add,le_refl]
  | succ k ih =>
    let head := one tape
    let amount := (samples one (k+1) tape).2+4
    have fits {x : ℕ} (le : x ≤ amount) : x.size ≤ B :=
      (Nat.size_le_size le).trans width
    have h4 : (4 : ℕ).size ≤ B := fits (Nat.le_add_left _ _)
    have fee := samples_step_fee one k tape
    have hh : head.2.size ≤ B := fits (by
      change (one tape).2 ≤ (samples one (k+1) tape).2+4
      rw [fee]
      omega)
    simp only [samplesWithCharges]
    cases h : (one tape).1 with
    | none =>
      have step := BinaryNaturalOperations.add_paid hh h4
      change (BinaryNaturalOperations.add head.2 4).2+4 ≤ _
      simp only [sampleControlBudget,Nat.succ_mul]
      omega
    | some item =>
      obtain ⟨first,rest⟩ := item
      let tail := samplesWithCharges one k rest
      let sum := BinaryNaturalOperations.add head.2 tail.1.2
      have earlier : tail.1=samples one k rest := samplesWithCharges_reference one k rest
      have whole : (samples one (k+1) tape).2=head.2+tail.1.2+4 := by
        rw [fee,h,Option.map_some,Option.getD_some,earlier]
      have tailWidth : ((samples one k rest).2+4).size ≤ B := fits (by
        rw [← earlier]
        change tail.1.2+4 ≤ (samples one (k+1) tape).2+4
        rw [whole]
        omega)
      have chargeWidth : tail.1.2.size ≤ B := fits (by
        change tail.1.2 ≤ (samples one (k+1) tape).2+4
        rw [whole]
        omega)
      have sumWidth : sum.1.size ≤ B := by
        rw [show sum.1=head.2+tail.1.2 from BinaryNaturalOperations.add_value ..]
        apply fits
        change head.2+tail.1.2 ≤ (samples one (k+1) tape).2+4
        rw [whole]
        omega
      have a : sum.2 ≤ BinaryRawRational.budget B+4 := BinaryNaturalOperations.add_paid hh chargeWidth
      have b := BinaryNaturalOperations.add_paid sumWidth h4
      have remaining : tail.2 ≤ k*sampleControlBudget B+1 := ih rest tailWidth
      change tail.2+sum.2+(BinaryNaturalOperations.add sum.1 4).2+8 ≤ _
      rw [Nat.succ_mul]
      unfold sampleControlBudget at remaining ⊢
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

/-- Carry measured sample accumulation and the two outer binary sums
through the same amplification and selection execution. -/
def runWithPlanScalarWork {n : ℕ} (D : BinaryFractionalGuesses.Input n)
    (round : PaidVertexSampling.Runner n) (roundBound extra confidence : ℕ) (plan : PhysicalCoverReader.Plan n)
    (dispatch readback : ℕ) (tape : Bits) : Read (Result n) × ℕ :=
  let setup := BinaryAmplificationPreparation.prepare D.costs roundBound extra confidence
  let all := samplesWithCharges (PaidVertexSampling.fromPlanWith D setup.costs round setup.trials plan) (extra+1) tape
  let chosen : Read (Result n) := match all.1.1 with
    | none => Read.failure
    | some (cuts,rest) => finish D.costs extra setup.paid dispatch readback cuts rest
  let selected := BinaryNaturalOperations.add all.1.2 chosen.2
  let total := BinaryNaturalOperations.add setup.paid selected.1
  ((chosen.1,total.1),all.2+selected.2+total.2+8)

theorem runWithPlanScalarWork_reference {n : ℕ} (D : BinaryFractionalGuesses.Input n)
    (round : PaidVertexSampling.Runner n) (roundBound extra confidence : ℕ) (plan : PhysicalCoverReader.Plan n)
    (dispatch readback : ℕ) (tape : Bits) :
    (runWithPlanScalarWork D round roundBound extra confidence plan dispatch readback tape).1 =
      runWithPlan D round roundBound extra confidence plan dispatch readback tape := by
  let setup := BinaryAmplificationPreparation.prepare D.costs roundBound extra confidence
  let all := samples (PaidVertexSampling.fromPlanWith D setup.costs round setup.trials plan) (extra+1) tape
  simp only [runWithPlanScalarWork,runWithPlan,samplesWithCharges_reference,BinaryNaturalOperations.add_value,
    Read.bind_value,bind_charge]
  change
    (_,
      setup.paid+(all.2+(match all.1 with
        | none => (Read.failure : Read (Result n))
        | some (cuts,rest) => finish D.costs extra setup.paid dispatch readback cuts rest).2)) =
    (all.1.bind (fun (cuts,rest) => (finish D.costs extra setup.paid dispatch readback cuts rest).1),
      setup.paid+(all.2+(all.1.map (fun (cuts,rest) =>
        (finish D.costs extra setup.paid dispatch readback cuts rest).2)).getD 0))
  cases all.1 <;> rfl

theorem runWithPlanScalarWork_paid {n B : ℕ} (D : BinaryFractionalGuesses.Input n)
    (round : PaidVertexSampling.Runner n) (roundBound extra confidence : ℕ) (plan : PhysicalCoverReader.Plan n)
    (dispatch readback : ℕ) (tape : Bits)
    (totalWidth : ((runWithPlan D round roundBound extra confidence plan dispatch readback tape).2+4).size ≤ B) :
    (runWithPlanScalarWork D round roundBound extra confidence plan dispatch readback tape).2 ≤
      (extra+2)*sampleControlBudget B+1 := by
  let setup := BinaryAmplificationPreparation.prepare D.costs roundBound extra confidence
  let one := PaidVertexSampling.fromPlanWith D setup.costs round setup.trials plan
  let all := samplesWithCharges one (extra+1) tape
  let chosen : Read (Result n) := match all.1.1 with
    | none => Read.failure
    | some (cuts,rest) => finish D.costs extra setup.paid dispatch readback cuts rest
  let selected := BinaryNaturalOperations.add all.1.2 chosen.2
  let total := BinaryNaturalOperations.add setup.paid selected.1
  have eq : total.1=(runWithPlan D round roundBound extra confidence plan dispatch readback tape).2 :=
    congrArg (fun r : Read (Result n) => r.2)
      (runWithPlanScalarWork_reference D round roundBound extra confidence plan dispatch readback tape)
  have projected : setup.paid+(all.1.2+chosen.2) =
      (runWithPlan D round roundBound extra confidence plan dispatch readback tape).2 :=
    by simpa only [total,selected,BinaryNaturalOperations.add_value] using eq
  have envelope {x : ℕ} (h : x ≤ setup.paid+(all.1.2+chosen.2)) : x.size ≤ B := by
    exact (Nat.size_le_size ((h.trans_eq projected).trans (Nat.le_add_right _ _))).trans totalWidth
  have left : all.1.2.size≤B := envelope (by omega)
  have right : chosen.2.size≤B := envelope (by omega)
  have selectedWidth : selected.1.size≤B := by
    rw [show selected.1=all.1.2+chosen.2 from BinaryNaturalOperations.add_value ..]
    exact envelope (Nat.le_add_left _ _)
  have setupWidth : setup.paid.size≤B := envelope (Nat.le_add_right _ _)
  have sampleWidth : ((samples one (extra+1) tape).2+4).size ≤ B := by
    have seen : all.1=samples one (extra+1) tape := samplesWithCharges_reference one _ _
    rw [← seen]
    apply (Nat.size_le_size ?_).trans totalWidth
    rw [← projected]
    omega
  have before : all.2 ≤ (extra+1)*sampleControlBudget B+1 :=
    samplesWithCharges_paid one (extra+1) tape sampleWidth
  have sum₁ : selected.2 ≤ BinaryRawRational.budget B+4 := BinaryNaturalOperations.add_paid left right
  have sum₂ : total.2 ≤ BinaryRawRational.budget B+4 := BinaryNaturalOperations.add_paid setupWidth selectedWidth
  change all.2+selected.2+total.2+8 ≤ _
  change _ ≤ ((extra+1)+1)*sampleControlBudget B+1
  rw [Nat.add_mul,Nat.one_mul]
  unfold sampleControlBudget at before ⊢
  omega

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
