import DirectedFlowCutGap.PhysicalAmplifiedVertexSolver
import DirectedFlowCutGap.PhysicalVertexRoundingCost

/-! Bound the actual row selection and amplification along each successful tape. -/

namespace DirectedFlowCutGap.PhysicalAmplifiedVertexCost

open BinaryArithmetic BinaryFractionalRows BinaryRational
open RetainedGridState (Flags)
open EncodedVertexSolver ChargedPhysicalVertexSolver

private theorem select_paid {n B budget : ℕ} {costs : Row n} (head : Flags n × ℕ)
    (tail : Option (ChargedCutSelection.Scored costs) × ℕ)
    (hB : 1 ≤ B) (fits : ∀ i, StoredBounded (get costs i) B) (paid : head.2 ≤ budget)
    (stored : ∀ s ∈ tail.1, StoredBounded s.price (n*(B+1)+1)) :
    let r := ChargedCutSelection.select head tail
    (∀ s ∈ r.1, StoredBounded s.price (n*(B+1)+1)) ∧
      r.2 ≤ tail.2+ChargedCutSelection.rowBound n B budget := by
  let score := BinaryCutPriceSelection.maskScore costs head.1
  let a : ChargedCutSelection.Scored costs :=
    ⟨head.1,score.1,BinaryCutPriceSelection.maskScore_decodes costs head.1⟩
  obtain ⟨width,price⟩ := BinaryCutPriceSelection.maskScore_charge costs head.1 hB fits
  change StoredBounded a.price (n*(B+1)+1) at width
  change score.2 ≤ sumBound n B at price
  rcases tail with ⟨scored,charge⟩
  cases scored with
  | none =>
    change (∀ s ∈ some a, StoredBounded s.price (n*(B+1)+1)) ∧
      head.2+charge+score.2+10 ≤ charge+ChargedCutSelection.rowBound n B budget
    refine ⟨fun u mem => (Option.mem_some_iff.mp mem).symm ▸ width,?_⟩
    unfold ChargedCutSelection.rowBound
    omega
  | some b =>
    have wb := stored b (by simp)
    let cmp := BinaryRational.le a.price b.price
    have comparison : cmp.2 ≤ 2048*(n*(B+1)+2)^2 := le_charge width wb
    change (∀ s ∈ some (if cmp.1 then a else b), StoredBounded s.price (n*(B+1)+1)) ∧
      head.2+charge+score.2+10+cmp.2 ≤ charge+ChargedCutSelection.rowBound n B budget
    constructor
    · split
      · exact fun u mem => (Option.mem_some_iff.mp mem).symm ▸ width
      · exact fun u mem => (Option.mem_some_iff.mp mem).symm ▸ wb
    · unfold ChargedCutSelection.rowBound
      omega

private theorem chooseRows_paid {n B : ℕ} (D : BinaryFractionalGuesses.Input n)
    (round : PhysicalVertexSampling.Runner n) (T budget : ℕ)
    (hB : 1 ≤ B) (fits : ∀ i, StoredBounded (get D.costs i) B)
    (rows : List (FractionalCoverRawCore.RawRow n)) (tape : Bits)
    (bound : ∀ y ∈ rows, ∀ tape (r : PhysicalIntegerRounding.Result n),
      round T (roundingInput (BinaryFractionalGuesses.decodeInput D) y) tape=some r → r.paid ≤ budget)
    {out : (Option (ChargedCutSelection.Scored D.costs) × ℕ) × Bits}
    (actual : PhysicalVertexSampling.chooseRows D round T rows tape=some out) :
    (∀ s ∈ out.1.1, StoredBounded s.price (n*(B+1)+1)) ∧
      out.1.2 ≤ rows.length*ChargedCutSelection.rowBound n B budget+1 := by
  induction rows generalizing tape out with
  | nil =>
    simp only [PhysicalVertexSampling.chooseRows,PhysicalVertexSampling.chooseRowsWith,Option.some.injEq] at actual
    rw [← actual]
    simp
  | cons y ys ih =>
    let input := roundingInput (BinaryFractionalGuesses.decodeInput D) y
    change ((round T input tape).bind fun a =>
      (PhysicalVertexSampling.chooseRows D round T ys a.suffix).map fun (best,rest) =>
        (ChargedCutSelection.select (a.mask,a.paid) best,rest))=some out at actual
    cases first : round T input tape with
    | none => simp [first] at actual
    | some a =>
      cases tail : PhysicalVertexSampling.chooseRows D round T ys a.suffix with
      | none => simp [first,tail] at actual
      | some late =>
        have hs := ih a.suffix (fun y mem => bound y (List.mem_cons_of_mem _ mem)) tail
        have selected := select_paid (a.mask,a.paid) late.1 hB fits (bound y List.mem_cons_self tape a first) hs.1
        simp only [first,tail,Option.bind_some,Option.map_some,Option.some.injEq] at actual
        rw [← actual]
        exact ⟨selected.1,selected.2.trans (by simp only [List.length_cons,Nat.add_mul,Nat.one_mul]; omega)⟩

theorem fromPlan_paid_on_rows {n B : ℕ} (D : BinaryFractionalGuesses.Input n)
    (round : PhysicalVertexSampling.Runner n) (T budget : ℕ)
    (hB : 1 ≤ B) (fits : ∀ i, StoredBounded (get D.costs i) B)
    (plan : PhysicalCoverReader.Plan n) (tape : Bits)
    (bound : ∀ rows, plan=.covers rows → ∀ y ∈ rows, ∀ tape (r : PhysicalIntegerRounding.Result n),
      round T (roundingInput (BinaryFractionalGuesses.decodeInput D) y) tape=some r → r.paid ≤ budget)
    {out : (Output n × ℕ) × Bits}
    (actual : PhysicalVertexSampling.fromPlan D round T plan tape=some out) :
    out.1.2 ≤ sampleBudget n B (rowsCount plan) budget := by
  cases plan with
  | invalid | infeasible _ | zero _ =>
    simp only [PhysicalVertexSampling.fromPlan,PhysicalVertexSampling.fromPlanWith,Option.some.injEq] at actual
    rw [← actual]
    simp [sampleBudget,rowsCount]
  | covers rows =>
    change (PhysicalVertexSampling.chooseRows D round T rows tape).map (fun (best,rest) =>
      (((ChargedCutSelection.result best).elim .invalid .cut,best.2+4*n+10),rest))=some out at actual
    cases h : PhysicalVertexSampling.chooseRows D round T rows tape with
    | none => simp [h] at actual
    | some x =>
      have paid := (chooseRows_paid D round T budget hB fits rows tape (bound rows rfl) h).2
      simp only [h,Option.map_some,Option.some.injEq] at actual
      rw [← actual]
      simp only [sampleBudget,rowsCount]
      omega

theorem fromPlan_paid {n B : ℕ} (D : BinaryFractionalGuesses.Input n)
    (round : PhysicalVertexSampling.Runner n) (T budget : ℕ)
    (hB : 1 ≤ B) (fits : ∀ i, StoredBounded (get D.costs i) B)
    (bound : ∀ input tape (r : PhysicalIntegerRounding.Result n), round T input tape=some r → r.paid ≤ budget)
    (plan : PhysicalCoverReader.Plan n) (tape : Bits) {out : (Output n × ℕ) × Bits}
    (actual : PhysicalVertexSampling.fromPlan D round T plan tape=some out) :
    out.1.2 ≤ sampleBudget n B (rowsCount plan) budget :=
  fromPlan_paid_on_rows D round T budget hB fits plan tape (fun _ _ _ _ => bound _) actual

private theorem samples_paid {A : Type} (one : Bits → Option ((A × ℕ) × Bits)) (budget : ℕ)
    (pay : ∀ tape a, one tape=some a → a.1.2 ≤ budget) (k : ℕ) (tape : Bits)
    {xs : Fin k → A × ℕ} {rest : Bits} (actual : PhysicalAmplifiedVertexSolver.samples one k tape=some (xs,rest)) :
    ∀ i, (xs i).2 ≤ budget := by
  induction k generalizing tape rest with
  | zero => exact fun i => i.elim0
  | succ k ih =>
    cases first : one tape with
    | none => simp [PhysicalAmplifiedVertexSolver.samples,first] at actual
    | some a =>
      rcases a with ⟨a,tail⟩
      cases restRun : PhysicalAmplifiedVertexSolver.samples one k tail with
      | none => simp [PhysicalAmplifiedVertexSolver.samples,first,restRun] at actual
      | some later =>
        rcases later with ⟨ys,suffix⟩
        simp only [PhysicalAmplifiedVertexSolver.samples,first,restRun,Option.bind_some,Option.map_some,
          Option.some.injEq,Prod.mk.injEq] at actual
        rw [← actual.1]
        exact Fin.cases (motive := fun i => (Fin.cons (α := fun _ => A × ℕ) a ys i).2 ≤ budget)
          (pay tape (a,tail) first) (ih tail restRun)

private theorem amplification_paid {n B : ℕ} (D : BinaryFractionalGuesses.Input n) (extra budget : ℕ)
    (hB : 1 ≤ B) (fits : ∀ i, StoredBounded (get D.costs i) B)
    (xs : Fin (extra+1) → Output n × ℕ) (paid : ∀ i, (xs i).2 ≤ budget) :
    (ChargedAmplification.select D.costs extra xs).2 ≤ ChargedAmplification.budget extra n B budget := by
  have sum : (List.ofFn fun i => (xs i).2).sum ≤ (extra+1)*budget := by
    rw [List.sum_ofFn]
    calc
      _ ≤ ∑ _i : Fin (extra+1), budget := Finset.sum_le_sum (fun i _ => paid i)
      _ = _ := by simp
  have minimum := (BinaryCutPriceSelection.minimum_charge
    (BinaryCutPriceSelection.cutScore D.costs) extra (fun i => (xs i).1)
    (n*(B+1)+1) (sumBound n B)
    (fun i => BinaryCutPriceSelection.cutScore_charge D.costs (xs i).1 hB fits)).2
  change (BinaryCutPriceSelection.minimum _ _ _).charge ≤ BinaryCutPriceSelection.selectionBound extra n B at minimum
  dsimp only [ChargedAmplification.select]
  unfold ChargedAmplification.budget
  omega

theorem run_paid_on_rows {n B : ℕ} (D : BinaryFractionalGuesses.Input n) (round : PhysicalVertexSampling.Runner n)
    (roundBound extra confidence cost : ℕ) (tape : Bits)
    (hB : 1 ≤ B) (fits : ∀ i, StoredBounded (get D.costs i) B)
    (bound : ∀ rows, PhysicalCoverReader.plan (BinaryFractionalGuesses.solveInput D).1=.covers rows →
      ∀ y ∈ rows, ∀ tape (r : PhysicalIntegerRounding.Result n),
        round (trialLimit (BinaryFractionalGuesses.decodeInput D) roundBound extra confidence)
          (roundingInput (BinaryFractionalGuesses.decodeInput D) y) tape=some r → r.paid ≤ cost)
    {out : PhysicalAmplifiedVertexSolver.Result n}
    (h : PhysicalAmplifiedVertexSolver.run D round roundBound extra confidence tape=some out) :
    out.dispatch ≤ PhysicalSolverCharges.dispatchBudget D ∧
    out.readback ≤ PhysicalSolverCharges.lookupBudget D ∧
    out.roundingAndSelection ≤ budget (BinaryFractionalGuesses.decodeInput D) B extra cost+
      BinaryAmplificationPreparation.budget (n+B+roundBound+extra+confidence) := by
  obtain ⟨dispatch,lookup,source,hd,hl⟩ := PhysicalSourceReadback.run_eq D
  let plan := PhysicalCoverReader.plan (BinaryFractionalGuesses.solveInput D).1
  let G := BinaryFractionalGuesses.decodeInput D
  let T := trialLimit G roundBound extra confidence
  let one := PhysicalVertexSampling.fromPlan D round T plan
  let setup := BinaryAmplificationPreparation.prepare D.costs roundBound extra confidence
  have prep := BinaryAmplificationPreparation.prepare_paid D.costs roundBound extra confidence fits
    (x := n+B+roundBound+extra+confidence) (by omega) (by omega) (by omega) (by omega) (by omega)
  simp only [PhysicalAmplifiedVertexSolver.run,source,Option.bind_some,PhysicalAmplifiedVertexSolver.runWithPlan,
    BinaryAmplificationPreparation.costs_value,BinaryAmplificationPreparation.trials_value D] at h
  change ((PhysicalAmplifiedVertexSolver.samples one (extra+1) tape).map fun (cuts,rest) =>
    ⟨(ChargedAmplification.select D.costs extra cuts).1,rest,dispatch,lookup,
      (ChargedAmplification.select D.costs extra cuts).2+setup.paid⟩)=some out at h
  cases samples : PhysicalAmplifiedVertexSolver.samples one (extra+1) tape with
  | none => simp [samples] at h
  | some s =>
    rcases s with ⟨cuts,rest⟩
    simp only [samples,Option.map_some,Option.some.injEq] at h
    rw [← h]
    refine ⟨hd,hl,Nat.add_le_add ?_ prep⟩
    apply amplification_paid D extra _ hB fits cuts
    apply samples_paid one _ _ (extra+1) tape samples
    intro bits r ran
    apply (fromPlan_paid_on_rows D round T cost hB fits plan bits bound ran).trans
    have length : rowsCount plan ≤ rowLimit G := rowsCount_le D
    unfold sampleBudget
    gcongr

theorem run_paid {n B : ℕ} (D : BinaryFractionalGuesses.Input n) (round : PhysicalVertexSampling.Runner n)
    (roundBound extra confidence cost : ℕ) (tape : Bits)
    (hB : 1 ≤ B) (fits : ∀ i, StoredBounded (get D.costs i) B)
    (bound : ∀ input tape (r : PhysicalIntegerRounding.Result n),
      round (trialLimit (BinaryFractionalGuesses.decodeInput D) roundBound extra confidence) input tape=some r → r.paid ≤ cost)
    {out : PhysicalAmplifiedVertexSolver.Result n}
    (h : PhysicalAmplifiedVertexSolver.run D round roundBound extra confidence tape=some out) :
    out.dispatch ≤ PhysicalSolverCharges.dispatchBudget D ∧
    out.readback ≤ PhysicalSolverCharges.lookupBudget D ∧
    out.roundingAndSelection ≤ budget (BinaryFractionalGuesses.decodeInput D) B extra cost+
      BinaryAmplificationPreparation.budget (n+B+roundBound+extra+confidence) :=
  run_paid_on_rows D round roundBound extra confidence cost tape hB fits (fun _ _ _ _ => bound _) h

end DirectedFlowCutGap.PhysicalAmplifiedVertexCost
