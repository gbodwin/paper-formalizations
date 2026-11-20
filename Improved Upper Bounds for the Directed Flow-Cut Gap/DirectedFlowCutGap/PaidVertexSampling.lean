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
