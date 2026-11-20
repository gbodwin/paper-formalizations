import DirectedFlowCutGap.PhysicalAmplifiedVertexSolver

/-! The work of earlier rows remains available when a later row runs out of tape. -/
namespace DirectedFlowCutGap.PaidVertexSampling

open BinaryArithmetic BinaryFractionalRows BinaryRational EncodedVertexSolver
open RetainedGridState (Flags)
open PhysicalIntegerRounding (Result)
open PhysicalCoverAccess (Read)

abbrev Runner (n : ℕ) := ℕ → RoundingInput n → Bits → Read (Result n)

private theorem score_adds {n : ℕ} {costs : Row n} (mask : Flags n) (head tail : ℕ)
    (prior : Option (ChargedCutSelection.Scored costs)) :
    let s := ChargedCutSelection.select (mask,0) (prior,0)
    ChargedCutSelection.select (mask,head) (prior,tail) = (s.1,head+tail+s.2) := by
  unfold ChargedCutSelection.select
  dsimp only
  cases prior <;> simp only [Nat.zero_add,Nat.add_assoc]

private abbrev RowResult {n : ℕ} (D : BinaryFractionalGuesses.Input n) :=
  (Option (ChargedCutSelection.Scored D.costs) × ℕ) × Bits

private def selectResult {n : ℕ} {D : BinaryFractionalGuesses.Input n} (a : Result n)
    (tail : RowResult D) : Read (RowResult D) :=
  let score := ChargedCutSelection.select (a.mask,0) (tail.1.1,0)
  (some ((score.1,a.paid+tail.1.2+score.2),tail.2),score.2)

def chooseRowsWith {n : ℕ} (D : BinaryFractionalGuesses.Input n) (costs : FractionalCoverRawCore.RawRow n)
    (round : Runner n) (T : ℕ) : List (FractionalCoverRawCore.RawRow n) → Bits → Read (RowResult D)
  | [], tape => (some ((none,1),tape),1)
  | y::ys, tape =>
      let r : Read (RowResult D) := do
        let a ← round T ⟨D.adjacency,y,costs⟩ tape
        let rest ← chooseRowsWith D costs round T ys a.suffix
        selectResult a rest
      (r.1,r.2+4)

private theorem chooseRows_cons {n : ℕ} (D : BinaryFractionalGuesses.Input n)
    (costs : FractionalCoverRawCore.RawRow n) (round : Runner n) (T : ℕ)
    (y : FractionalCoverRawCore.RawRow n) (ys : List (FractionalCoverRawCore.RawRow n)) (tape : Bits) :
    let first := round T ⟨D.adjacency,y,costs⟩ tape
    chooseRowsWith D costs round T (y::ys) tape=match first.1 with
      | none => (none,first.2+4)
      | some a =>
        let rest := chooseRowsWith D costs round T ys a.suffix
        let chosen := match rest.1 with
          | none => Read.failure
          | some tail => selectResult a tail
        (chosen.1,first.2+rest.2+chosen.2+4) := by
  let first := round T ⟨D.adjacency,y,costs⟩ tape
  let more (a : Result n) := Read.bind (chooseRowsWith D costs round T ys a.suffix) (selectResult a)
  change ((Read.bind first more).1,(Read.bind first more).2+4)=_
  cases h : first.1 with
  | none =>
    simp only [Read.bind,h]
    rfl
  | some a =>
    simp only [Read.bind,h,more]
    cases (chooseRowsWith D costs round T ys a.suffix).1 with
    | none => rfl
    | some result =>
      simp only [Nat.add_assoc]
      rfl

private def selectResultWithControl {n : ℕ} {D : BinaryFractionalGuesses.Input n} (a : Result n)
    (tail : RowResult D) : Read (RowResult D) × ℕ :=
  let score := ChargedCutSelection.selectWithControl (a.mask,0) (tail.1.1,0)
  let paid := CachedScalarRead.sumMeasured [a.paid,tail.1.2,score.1.2]
  ((some ((score.1.1,paid.1),tail.2),score.1.2),score.2+paid.2+4)

private theorem selectResultWithControl_reference {n : ℕ} {D : BinaryFractionalGuesses.Input n}
    (a : Result n) (tail : RowResult D) :
    (selectResultWithControl a tail).1=selectResult a tail := by
  simp only [selectResultWithControl,selectResult,ChargedCutSelection.selectWithControl_value,
    CachedScalarRead.sum_value,List.sum_cons,List.sum_nil,Nat.add_zero,Nat.add_assoc]

def chooseRowsWithSelectionWork {n : ℕ} (D : BinaryFractionalGuesses.Input n)
    (costs : FractionalCoverRawCore.RawRow n) (round : Runner n) (T : ℕ) :
    List (FractionalCoverRawCore.RawRow n) → Bits → Read (RowResult D) × ℕ
  | [], tape => ((some ((none,1),tape),1),1)
  | y::ys, tape =>
    let first := round T ⟨D.adjacency,y,costs⟩ tape
    match first.1 with
    | none =>
      let amount := BinaryNaturalOperations.add first.2 4
      ((none,amount.1),amount.2+4)
    | some a =>
      let rest := chooseRowsWithSelectionWork D costs round T ys a.suffix
      let chosen : Read (RowResult D) × ℕ := match rest.1.1 with
        | none => (Read.failure,0)
        | some tail => selectResultWithControl a tail
      let amount := CachedScalarRead.sumMeasured [first.2,rest.1.2,chosen.1.2,4]
      ((chosen.1.1,amount.1),rest.2+chosen.2+amount.2+8)

theorem chooseRowsWithSelectionWork_reference {n : ℕ} (D : BinaryFractionalGuesses.Input n)
    (costs : FractionalCoverRawCore.RawRow n) (round : Runner n) (T : ℕ)
    (rows : List (FractionalCoverRawCore.RawRow n)) (tape : Bits) :
    (chooseRowsWithSelectionWork D costs round T rows tape).1=chooseRowsWith D costs round T rows tape := by
  induction rows generalizing tape with
  | nil => rfl
  | cons y ys ih =>
    let first := round T ⟨D.adjacency,y,costs⟩ tape
    simp only [chooseRowsWithSelectionWork,chooseRows_cons]
    cases h : first.1 with
    | none =>
      simp only [BinaryNaturalOperations.add_value]
    | some a =>
      dsimp only
      rw [ih a.suffix]
      let rest := chooseRowsWith D costs round T ys a.suffix
      cases later : rest.1 with
      | none =>
        simp only [Read.failure,CachedScalarRead.sum_value,List.sum_cons,List.sum_nil,Nat.add_zero,Nat.add_assoc]
      | some tail =>
        simp only [selectResultWithControl_reference,
          CachedScalarRead.sum_value,List.sum_cons,List.sum_nil,Nat.add_zero,Nat.add_assoc]

private def selectedRowBudget {R : Type*} [Semiring R] (n B : R) : R :=
  ChargedCutSelection.rowSelectionBudget n B+3*(96*(B+2)^2+4)+5

private theorem selectResultWithControl_paid {n B : ℕ} {D : BinaryFractionalGuesses.Input n}
    (a : Result n) (tail : RowResult D)
    (charge : (selectResult a tail).2.size≤B)
    (value : (a.paid+tail.1.2+(selectResult a tail).2).size≤B) :
    (selectResultWithControl a tail).2 ≤ selectedRowBudget n B := by
  let chosen := ChargedCutSelection.selectWithControl (a.mask,0) (tail.1.1,0)
  let prior := selectResult a tail
  let amounts := [a.paid,tail.1.2,chosen.1.2]
  have price : chosen.2≤ChargedCutSelection.rowSelectionBudget n B :=
    ChargedCutSelection.selectWithControl_paid (a.mask,0) (tail.1.1,0) charge
  have same : chosen.1.2=prior.2 := congrArg Prod.snd (ChargedCutSelection.selectWithControl_value ..)
  have sumWidth : amounts.sum.size≤B := by
    simpa only [amounts,same,List.sum_cons,List.sum_nil,Nat.add_zero,Nat.add_assoc] using value
  have addition := CachedScalarRead.sum_paid amounts sumWidth
  simp only [amounts,List.length_cons,List.length_nil] at addition
  change chosen.2+(CachedScalarRead.sumMeasured [a.paid,tail.1.2,chosen.1.2]).2+4≤_
  unfold selectedRowBudget
  omega

def rowWorkBudget {R : Type*} [Semiring R] (n B : R) : R :=
  selectedRowBudget n B+4*(96*(B+2)^2+4)+9+BinaryRawRational.budget B+8

theorem chooseRowsWithSelectionWork_paid {n B : ℕ} (D : BinaryFractionalGuesses.Input n)
    (costs : FractionalCoverRawCore.RawRow n) (round : Runner n) (T : ℕ)
    (rows : List (FractionalCoverRawCore.RawRow n)) (tape : Bits)
    (paid : (chooseRowsWith D costs round T rows tape).2.size≤B)
    (returned : ∀ out ∈ (chooseRowsWith D costs round T rows tape).1, out.1.2.size≤B) :
    (chooseRowsWithSelectionWork D costs round T rows tape).2≤rows.length*rowWorkBudget n B+1 := by
  induction rows generalizing tape with
  | nil => simp only [chooseRowsWithSelectionWork,List.length_nil,Nat.zero_mul,Nat.zero_add,le_refl]
  | cons y ys ih =>
    let first := round T ⟨D.adjacency,y,costs⟩ tape
    let before := chooseRowsWith D costs round T (y::ys) tape
    cases h : first.1 with
    | none =>
      have original : before=(none,first.2+4) := by
        unfold before
        rw [chooseRows_cons]
        change (match first.1 with | none => _ | some _ => _) = _
        rw [h]
      have cap : (first.2+4).size≤B := by simpa only [before,original] using paid
      have a := (Nat.size_le_size (Nat.le_add_right first.2 4)).trans cap
      have b := (Nat.size_le_size (Nat.le_add_left 4 first.2)).trans cap
      have add := BinaryNaturalOperations.add_paid a b
      simp only [chooseRowsWithSelectionWork,show (round T ⟨D.adjacency,y,costs⟩ tape).1=none from h]
      change (BinaryNaturalOperations.add first.2 4).2+4≤_
      rw [List.length_cons,Nat.add_mul,Nat.one_mul]
      unfold rowWorkBudget
      omega
    | some a =>
      let rest := chooseRowsWith D costs round T ys a.suffix
      let next := chooseRowsWithSelectionWork D costs round T ys a.suffix
      let chosen : Read (RowResult D) := match rest.1 with
        | none => Read.failure
        | some out => selectResult a out
      let measured : Read (RowResult D) × ℕ := match rest.1 with
        | none => (Read.failure,0)
        | some out => selectResultWithControl a out
      let fees := [first.2,rest.2,chosen.2,4]
      have original : before=(chosen.1,first.2+rest.2+chosen.2+4) := by
        unfold before
        rw [chooseRows_cons]
        change (match first.1 with | none => _ | some _ => _) = _
        rw [h]
      have sum : fees.sum=before.2 := by
        rw [original]
        simp only [fees,List.sum_cons,List.sum_nil,Nat.add_zero,Nat.add_assoc]
      have fits {x : ℕ} (rel : x≤fees.sum) : x.size≤B := by
        apply (Nat.size_le_size (rel.trans_eq sum)).trans paid
      have tailFee : rest.2.size≤B := fits (by simp only [fees,List.sum_cons,List.sum_nil]; omega)
      have headFee : chosen.2.size≤B := fits (by simp only [fees,List.sum_cons,List.sum_nil]; omega)
      have outputFits (out : RowResult D) (visible : rest.1=some out) :
          (a.paid+out.1.2+(selectResult a out).2).size≤B := by
        let s := ChargedCutSelection.select (a.mask,0) (out.1.1,0)
        let answer : RowResult D := ((s.1,a.paid+out.1.2+s.2),out.2)
        have whole : before.1=some answer := by
          rw [original]
          simp only [chosen,visible,selectResult,answer,s]
        exact returned answer (Option.mem_def.mpr whole)
      have tailFits : ∀ out ∈ rest.1, out.1.2.size≤B := by
        intro out present
        apply (Nat.size_le_size ?_).trans (outputFits out (Option.mem_def.mp present))
        omega
      have prior : next.2≤ys.length*rowWorkBudget n B+1 := ih a.suffix tailFee tailFits
      have same : measured.1=chosen := by
        unfold measured chosen
        cases rest.1 with
        | none => rfl
        | some result => exact selectResultWithControl_reference a result
      have selection : measured.2 ≤ selectedRowBudget n B := by
        unfold measured
        cases visible : rest.1 with
        | none => exact Nat.zero_le _
        | some out =>
          have one : (selectResult a out).2.size≤B := by simpa only [chosen,visible] using headFee
          exact selectResultWithControl_paid a out one (outputFits out visible)
      have amount := CachedScalarRead.sum_paid fees (fits (Nat.le_refl _))
      simp only [fees,List.length_cons,List.length_nil] at amount
      simp only [chooseRowsWithSelectionWork,show (round T ⟨D.adjacency,y,costs⟩ tape).1=some a from h,
        chooseRowsWithSelectionWork_reference]
      change next.2+measured.2+(CachedScalarRead.sumMeasured [first.2,rest.2,measured.1.2,4]).2+8≤_
      rw [same,List.length_cons,Nat.add_mul,Nat.one_mul]
      unfold rowWorkBudget at prior ⊢
      omega

theorem chooseRows_value {n : ℕ} (D : BinaryFractionalGuesses.Input n) (costs : FractionalCoverRawCore.RawRow n)
    (round : Runner n) (T : ℕ) (rows : List (FractionalCoverRawCore.RawRow n)) (tape : Bits) :
    (chooseRowsWith D costs round T rows tape).1 =
      PhysicalVertexSampling.chooseRowsWith D costs (fun T input tape => (round T input tape).1) T rows tape := by
  induction rows generalizing tape with
  | nil => rfl
  | cons y ys ih =>
      simp only [chooseRowsWith,PhysicalVertexSampling.chooseRowsWith,Read.bind_value]
      cases h : (round T ⟨D.adjacency,y,costs⟩ tape).1 with
      | none => rfl
      | some a =>
          simp only [Option.bind_some,← ih]
          cases tail : (chooseRowsWith D costs round T ys a.suffix).1 with
          | none => rfl
          | some pair =>
              rcases pair with ⟨⟨best,paid⟩,rest⟩
              simp only [selectResult,Option.bind_some,Option.map_some]
              rw [score_adds a.mask a.paid paid best]

private theorem select_paid {n B : ℕ} {D : BinaryFractionalGuesses.Input n}
    (a : Result n) (tail : RowResult D) (positive : 1 ≤ B)
    (cost : ∀ i, StoredBounded (get D.costs i) B)
    (bounded : ∀ s ∈ tail.1.1, StoredBounded s.price (n*(B+1)+1)) :
    (∀ r, (selectResult a tail).1=some r → ∀ s ∈ r.1.1, StoredBounded s.price (n*(B+1)+1)) ∧
      (selectResult a tail).2 ≤ ChargedCutSelection.rowBound n B 0 := by
  let scored := BinaryCutPriceSelection.maskScore D.costs a.mask
  let x : ChargedCutSelection.Scored D.costs :=
    ⟨a.mask,scored.1,BinaryCutPriceSelection.maskScore_decodes D.costs a.mask⟩
  obtain ⟨width,fee⟩ := BinaryCutPriceSelection.maskScore_charge D.costs a.mask positive cost
  change StoredBounded x.price (n*(B+1)+1) at width
  change scored.2 ≤ sumBound n B at fee
  rcases tail with ⟨⟨prior,paid⟩,rest⟩
  cases prior with
  | none =>
      constructor
      · intro r done s member
        have same : (some ((some x,a.paid+paid+(0+0+scored.2+10)),rest) : Option (RowResult D))=some r := done
        rw [← Option.some.inj same] at member
        exact (Option.mem_some_iff.mp member).symm ▸ width
      · change 0+0+scored.2+10 ≤ _
        unfold ChargedCutSelection.rowBound
        omega
  | some y =>
      have kept := bounded y (by simp)
      let compare := BinaryRational.le x.price y.price
      have cmp : compare.2 ≤ 2048*(n*(B+1)+2)^2 := le_charge width kept
      constructor
      · intro r done s member
        let chosen := if compare.1 then x else y
        have same : (some ((some chosen,a.paid+paid+(0+0+scored.2+10+compare.2)),rest) :
            Option (RowResult D))=some r := done
        rw [← Option.some.inj same] at member
        have stored : StoredBounded chosen.price (n*(B+1)+1) := by
          unfold chosen
          split
          · exact width
          · exact kept
        exact (Option.mem_some_iff.mp member).symm ▸ stored
      · change 0+0+scored.2+10+compare.2 ≤ _
        unfold ChargedCutSelection.rowBound
        omega

theorem chooseRows_paid {n B : ℕ} (D : BinaryFractionalGuesses.Input n)
    (costs : FractionalCoverRawCore.RawRow n) (round : Runner n) (T budget : ℕ)
    (positive : 1 ≤ B) (cost : ∀ i, StoredBounded (get D.costs i) B)
    (rows : List (FractionalCoverRawCore.RawRow n)) (tape : Bits)
    (bound : ∀ y ∈ rows, ∀ tape, (round T ⟨D.adjacency,y,costs⟩ tape).2 ≤ budget) :
    let r := chooseRowsWith D costs round T rows tape
    (∀ a, r.1=some a → ∀ s ∈ a.1.1, StoredBounded s.price (n*(B+1)+1)) ∧
      r.2 ≤ rows.length*(budget+ChargedCutSelection.rowBound n B 0+4)+1 := by
  induction rows generalizing tape with
  | nil => simp [chooseRowsWith]
  | cons y ys ih =>
      let head := round T ⟨D.adjacency,y,costs⟩ tape
      let tail (a : Result n) := chooseRowsWith D costs round T ys a.suffix
      let run : Read (RowResult D) := head >>= fun a => tail a >>= selectResult a
      change (∀ a, run.1=some a → _) ∧ run.2+4 ≤ _
      have recursive (a : Result n) := ih a.suffix (fun y mem => bound y (List.mem_cons_of_mem _ mem))
      constructor
      · intro answer done s member
        change (head >>= fun a => tail a >>= selectResult a).1=some answer at done
        rw [Read.bind_value] at done
        cases first : head.1 with
        | none => simp [first] at done
        | some a =>
            simp only [first,Option.bind_some,Read.bind_value] at done
            cases later : (tail a).1 with
            | none => simp [later] at done
            | some rest =>
                simp only [later,Option.bind_some] at done
                exact (select_paid a rest positive cost ((recursive a).1 rest later)).1 answer done s member
      · have paid : run.2 ≤ budget+(ys.length*(budget+ChargedCutSelection.rowBound n B 0+4)+1+
            ChargedCutSelection.rowBound n B 0) := by
          apply Read.bind_bound (bound y List.mem_cons_self tape)
          intro a _
          apply Read.bind_bound (recursive a).2
          intro rest valid
          exact (select_paid a rest positive cost ((recursive a).1 rest valid)).2
        apply (Nat.add_le_add_right paid 4).trans_eq
        rw [List.length_cons,Nat.add_mul,Nat.one_mul]
        ac_rfl

def fromPlanWith {n : ℕ} (D : BinaryFractionalGuesses.Input n) (costs : FractionalCoverRawCore.RawRow n)
    (round : Runner n) (T : ℕ) : PhysicalCoverReader.Plan n → Bits → Read ((Output n × ℕ) × Bits)
  | .invalid,tape => (some ((.invalid,4*n+10),tape),4*n+10)
  | .infeasible d,tape => (some ((.infeasible d,4*n+10),tape),4*n+10)
  | .zero mask,tape => (some ((.cut mask,4*n+10),tape),4*n+10)
  | .covers rows,tape =>
      let choice := chooseRowsWith D costs round T rows tape
      (choice.1.map (fun (best,rest) => (((ChargedCutSelection.result best).elim .invalid .cut,best.2+4*n+10),rest)),
        choice.2+4*n+10)

def fromPlanWithSelectionWork {n : ℕ} (D : BinaryFractionalGuesses.Input n) (costs : FractionalCoverRawCore.RawRow n)
    (round : Runner n) (T : ℕ) (plan : PhysicalCoverReader.Plan n) (tape : Bits) : Read ((Output n × ℕ) × Bits) × ℕ :=
  match plan with
  | .covers rows =>
    let choice := chooseRowsWithSelectionWork D costs round T rows tape
    let overhead := 4*n+10
    let billed := CachedScalarRead.sumMeasured [choice.1.2,4*n,10]
    match choice.1.1 with
    | none => ((none,billed.1),choice.2+billed.2+4)
    | some (best,rest) =>
      let charge := BinaryNaturalOperations.add best.2 overhead
      ((some (((ChargedCutSelection.result best).elim .invalid .cut,charge.1),rest),billed.1),
        choice.2+billed.2+charge.2+8)
  | _ => (fromPlanWith D costs round T plan tape,0)

theorem fromPlanWithSelectionWork_reference {n : ℕ} (D : BinaryFractionalGuesses.Input n)
    (costs : FractionalCoverRawCore.RawRow n) (round : Runner n) (T : ℕ)
    (plan : PhysicalCoverReader.Plan n) (tape : Bits) :
    (fromPlanWithSelectionWork D costs round T plan tape).1=fromPlanWith D costs round T plan tape := by
  cases plan with
  | invalid | infeasible _ | zero _ => rfl
  | covers rows =>
    simp only [fromPlanWithSelectionWork,fromPlanWith,chooseRowsWithSelectionWork_reference]
    cases (chooseRowsWith D costs round T rows tape).1 with
    | none => simp only [Option.map_none,CachedScalarRead.sum_value,List.sum_cons,List.sum_nil,
        Nat.add_zero,Nat.add_assoc]
    | some out =>
      obtain ⟨best,rest⟩ := out
      simp only [Option.map_some,BinaryNaturalOperations.add_value,CachedScalarRead.sum_value,List.sum_cons,
        List.sum_nil,Nat.add_zero,Nat.add_assoc]

def planWorkBudget {R : Type*} [Semiring R] (n count B : R) : R :=
  count*rowWorkBudget n B+3*(96*(B+2)^2+4)+BinaryRawRational.budget B+14

theorem planWorkBudget_mono {n count B n' count' B' : ℕ}
    (dimensions : n≤n') (rows : count≤count') (width : B≤B') :
    planWorkBudget n count B ≤ planWorkBudget n' count' B' := by
  unfold planWorkBudget rowWorkBudget selectedRowBudget ChargedCutSelection.rowSelectionBudget
    BinaryRawRational.budget
  gcongr
  exact BinaryCutPriceSelection.fieldControlBudget_mono dimensions

open Polynomial in
theorem planWorkBudget_eval (n count B : Polynomial ℕ) (x : ℕ) :
    (planWorkBudget n count B).eval x=planWorkBudget (n.eval x) (count.eval x) (B.eval x) := by
  simp only [planWorkBudget,rowWorkBudget,selectedRowBudget,ChargedCutSelection.rowSelectionBudget,
    BinaryCutPriceSelection.fieldControlBudget_eval,BinaryRawRational.budget,eval_add,eval_mul,eval_pow,eval_ofNat]

theorem fromPlanWithSelectionWork_paid {n B : ℕ} (D : BinaryFractionalGuesses.Input n)
    (costs : FractionalCoverRawCore.RawRow n) (round : Runner n) (T : ℕ)
    (plan : PhysicalCoverReader.Plan n) (tape : Bits)
    (paid : (fromPlanWith D costs round T plan tape).2.size≤B)
    (returned : ∀ out ∈ (fromPlanWith D costs round T plan tape).1, out.1.2.size≤B) :
    (fromPlanWithSelectionWork D costs round T plan tape).2≤
      planWorkBudget n (ChargedPhysicalVertexSolver.rowsCount plan) B := by
  cases plan with
  | invalid | infeasible _ | zero _ => exact Nat.zero_le _
  | covers rows =>
    let old := chooseRowsWith D costs round T rows tape
    let actual := chooseRowsWithSelectionWork D costs round T rows tape
    let overhead := 4*n+10
    let amounts := [old.2,4*n,10]
    have billed : amounts.sum.size≤B := by
      simpa only [amounts,fromPlanWith,List.sum_cons,List.sum_nil,Nat.add_zero,Nat.add_assoc] using paid
    have previous : old.2.size≤B :=
      (Nat.size_le_size (show old.2≤amounts.sum by simp [amounts])).trans billed
    have exposed (result : RowResult D) (ready : old.1=some result) : (result.1.2+overhead).size≤B := by
      let out : (Output n × ℕ) × Bits :=
        (((ChargedCutSelection.result result.1).elim .invalid .cut,result.1.2+overhead),result.2)
      have found : (fromPlanWith D costs round T (.covers rows) tape).1=some out := by
        simp only [fromPlanWith,show (chooseRowsWith D costs round T rows tape).1=some result from ready,
          Option.map_some,out,overhead,Nat.add_assoc]
      exact returned out (Option.mem_def.mpr found)
    have rowValues : ∀ result ∈ old.1, result.1.2.size≤B := fun result ready =>
      (Nat.size_le_size (Nat.le_add_right _ _)).trans (exposed result (Option.mem_def.mp ready))
    have rowWork : actual.2≤rows.length*rowWorkBudget n B+1 :=
      chooseRowsWithSelectionWork_paid D costs round T rows tape previous rowValues
    have sum := CachedScalarRead.sum_paid amounts billed
    simp only [amounts,List.length_cons,List.length_nil] at sum
    simp only [fromPlanWithSelectionWork,chooseRowsWithSelectionWork_reference,ChargedPhysicalVertexSolver.rowsCount]
    cases ready : old.1 with
    | none =>
      change actual.2+(CachedScalarRead.sumMeasured [old.2,4*n,10]).2+4≤_
      unfold planWorkBudget
      omega
    | some result =>
      obtain ⟨best,rest⟩ := result
      have total := exposed (best,rest) ready
      have b : best.2.size≤B := (Nat.size_le_size (Nat.le_add_right _ _)).trans total
      have d : overhead.size≤B := (Nat.size_le_size (Nat.le_add_left _ _)).trans total
      have extra := BinaryNaturalOperations.add_paid b d
      change actual.2+(CachedScalarRead.sumMeasured [old.2,4*n,10]).2+
        (BinaryNaturalOperations.add best.2 overhead).2+8≤_
      unfold planWorkBudget
      omega

theorem fromPlan_value {n : ℕ} (D : BinaryFractionalGuesses.Input n) (costs : FractionalCoverRawCore.RawRow n)
    (round : Runner n) (T : ℕ) (plan : PhysicalCoverReader.Plan n) (tape : Bits) :
    (fromPlanWith D costs round T plan tape).1 =
      PhysicalVertexSampling.fromPlanWith D costs (fun T input tape => (round T input tape).1) T plan tape := by
  cases plan with
  | invalid | infeasible _ | zero _ => rfl
  | covers _ => simp only [fromPlanWith,PhysicalVertexSampling.fromPlanWith,chooseRows_value]

theorem fromPlan_paid {n B : ℕ} (D : BinaryFractionalGuesses.Input n)
    (costs : FractionalCoverRawCore.RawRow n) (round : Runner n) (T budget : ℕ)
    (positive : 1 ≤ B) (cost : ∀ i, StoredBounded (get D.costs i) B)
    (plan : PhysicalCoverReader.Plan n) (tape : Bits)
    (bound : ∀ rows, plan=.covers rows → ∀ y ∈ rows, ∀ tape,
      (round T ⟨D.adjacency,y,costs⟩ tape).2 ≤ budget) :
    (fromPlanWith D costs round T plan tape).2 ≤
      ChargedPhysicalVertexSolver.rowsCount plan*(budget+ChargedCutSelection.rowBound n B 0+4)+4*n+11 := by
  cases plan with
  | invalid | infeasible _ | zero _ => simp [fromPlanWith,ChargedPhysicalVertexSolver.rowsCount]
  | covers rows =>
      have paid := (chooseRows_paid D costs round T budget positive cost rows tape (bound rows rfl)).2
      simp only [fromPlanWith,ChargedPhysicalVertexSolver.rowsCount]
      omega

/-- The continuation sees the same paid result. Only the work returned by
reached branches can increase. -/
theorem bind_extra {A B : Type} {a b : Read A} {f g : A → Read B} {d e : ℕ}
    (same : b.1=a.1) (extra : b.2 ≤ a.2+d)
    (later : ∀ x, a.1=some x → (g x).2 ≤ (f x).2+e) :
    (b >>= g).2 ≤ (a >>= f).2+d+e := by
  change (Read.bind b g).2 ≤ (Read.bind a f).2+d+e
  unfold Read.bind
  rw [same]
  cases first : a.1 with
  | none => exact extra.trans (Nat.le_add_right _ _)
  | some x =>
    have tail := later x first
    dsimp only
    omega

theorem chooseRows_extra_on_rows {n : ℕ} (D : BinaryFractionalGuesses.Input n) (costs : FractionalCoverRawCore.RawRow n)
    (old newer : Runner n) (T cap : ℕ) (rows : List (FractionalCoverRawCore.RawRow n)) (tape : Bits)
    (same : ∀ t input bits, (newer t input bits).1=(old t input bits).1)
    (extra : ∀ y ∈ rows, ∀ bits, (newer T ⟨D.adjacency,y,costs⟩ bits).2 ≤
      (old T ⟨D.adjacency,y,costs⟩ bits).2+cap) :
    (chooseRowsWith D costs newer T rows tape).2 ≤
      (chooseRowsWith D costs old T rows tape).2+rows.length*cap := by
  have sameRounds : (fun t input bits => (newer t input bits).1) = (fun t input bits => (old t input bits).1) :=
    funext fun t => funext fun i => funext fun bits => same t i bits
  induction rows generalizing tape with
  | nil => simp [chooseRowsWith]
  | cons y ys ih =>
      let a := old T ⟨D.adjacency,y,costs⟩ tape
      let b := newer T ⟨D.adjacency,y,costs⟩ tape
      let prior (h : Result n) := chooseRowsWith D costs old T ys h.suffix
      let current (h : Result n) := chooseRowsWith D costs newer T ys h.suffix
      have nextSame (h : Result n) : (current h).1=(prior h).1 := by
        simp only [current,prior,chooseRows_value,sameRounds]
      have tail (h : Result n) :
          (current h >>= selectResult h).2 ≤ (prior h >>= selectResult h).2+ys.length*cap := by
        have paid : (current h).2 ≤ (prior h).2+ys.length*cap :=
          ih h.suffix (fun q hq bits => extra q (List.mem_cons_of_mem y hq) bits)
        exact (bind_extra (e := 0) (nextSame h) paid (fun _ _ => Nat.le_add_right _ _)).trans_eq (Nat.add_zero _)
      have paid : (b >>= fun h => current h >>= selectResult h).2 ≤
          (a >>= fun h => prior h >>= selectResult h).2+cap+ys.length*cap :=
        bind_extra (same T _ _) (extra y List.mem_cons_self tape) (fun h _ => tail h)
      unfold chooseRowsWith
      simp only [List.length_cons,Nat.add_mul,Nat.one_mul]
      change (b >>= fun h => current h >>= selectResult h).2+4 ≤
        (a >>= fun h => prior h >>= selectResult h).2+4+(ys.length*cap+cap)
      omega

theorem chooseRows_extra {n : ℕ} (D : BinaryFractionalGuesses.Input n) (costs : FractionalCoverRawCore.RawRow n)
    (old newer : Runner n) (T cap : ℕ) (rows : List (FractionalCoverRawCore.RawRow n)) (tape : Bits)
    (same : ∀ t input bits, (newer t input bits).1=(old t input bits).1)
    (extra : ∀ input bits, (newer T input bits).2 ≤ (old T input bits).2+cap) :
    (chooseRowsWith D costs newer T rows tape).2 ≤
      (chooseRowsWith D costs old T rows tape).2+rows.length*cap :=
  chooseRows_extra_on_rows D costs old newer T cap rows tape same (fun _ _ bits => extra _ bits)

theorem fromPlan_extra_on_rows {n : ℕ} (D : BinaryFractionalGuesses.Input n) (costs : FractionalCoverRawCore.RawRow n)
    (old newer : Runner n) (T cap : ℕ) (plan : PhysicalCoverReader.Plan n) (tape : Bits)
    (same : ∀ t input bits, (newer t input bits).1=(old t input bits).1)
    (extra : ∀ rows, plan=.covers rows → ∀ y ∈ rows, ∀ bits,
      (newer T ⟨D.adjacency,y,costs⟩ bits).2 ≤ (old T ⟨D.adjacency,y,costs⟩ bits).2+cap) :
    (fromPlanWith D costs newer T plan tape).2 ≤ (fromPlanWith D costs old T plan tape).2+
      ChargedPhysicalVertexSolver.rowsCount plan*cap := by
  cases plan with
  | invalid | infeasible _ | zero _ => simp [fromPlanWith,ChargedPhysicalVertexSolver.rowsCount]
  | covers rows =>
    have paid := chooseRows_extra_on_rows D costs old newer T cap rows tape same (extra rows rfl)
    simp only [fromPlanWith,ChargedPhysicalVertexSolver.rowsCount]
    omega

theorem fromPlan_extra {n : ℕ} (D : BinaryFractionalGuesses.Input n) (costs : FractionalCoverRawCore.RawRow n)
    (old newer : Runner n) (T cap : ℕ) (plan : PhysicalCoverReader.Plan n) (tape : Bits)
    (same : ∀ t input bits, (newer t input bits).1=(old t input bits).1)
    (extra : ∀ input bits, (newer T input bits).2 ≤ (old T input bits).2+cap) :
    (fromPlanWith D costs newer T plan tape).2 ≤ (fromPlanWith D costs old T plan tape).2+
      ChargedPhysicalVertexSolver.rowsCount plan*cap :=
  fromPlan_extra_on_rows D costs old newer T cap plan tape same (fun _ _ _ _ bits => extra _ bits)

end DirectedFlowCutGap.PaidVertexSampling
