import DirectedFlowCutGap.BinaryApproximatePacking

/-!
# The actual retained answers determine the pathwise packing schedule

Replay and natural indexing here are proof-side specifications. The executable
controller continues to use binary fuel and its actual monadic provider. No
caller supplies a favorable transcript: the schedule is read from its retained
Answer list, and the erased cache-aware certificate proves same-state replay.
-/
namespace DirectedFlowCutGap.BinaryApproximatePackingTrace
open BinaryApproximatePacking BinaryArithmetic BinaryFractionalRows BinaryRational

variable {m : ℕ}

def replayChoices (c : Row m) : List (Choice m) → State m → State m
  | [],s => s
  | q::qs,s => replayChoices c qs (BinaryFractionalCore.step c (cached q) s).1

theorem replay_append (c : Row m) (as bs : List (Choice m)) (s : State m) :
    replayChoices c (as++bs) s=replayChoices c bs (replayChoices c as s) := by
  induction as generalizing s with
  | nil => rfl
  | cons a as ih => exact ih _

theorem replay_trace {c : Row m} {columns : Set (FractionalCover.Column m)}
    {k : ℕ} {p p' : Pending c columns} {s t : State m} {answers : List (Answer m)}
    (h : Trace c columns k p s p' t answers) (hp : p'=none) :
    replayChoices c (p.toList.map Subtype.val++answers.map Answer.choice) s=t := by
  revert hp
  induction h with
  | zero => intro hp;cases hp;rfl
  | succ head tail ih =>
      intro hp
      have ht := ih hp
      cases head with
      | stopped => simpa using ht
      | cached => simpa [replayChoices] using ht
      | fresh => simpa [replayChoices] using ht

theorem input_replay {c : Row m} {columns : Set (FractionalCover.Column m)}
    (r : InputResult c columns) (hm : 0 < m)
    (hc : ∀ i, 0 < FractionalCover.value (capacities c) i) :
    replayChoices c (r.answers.map Answer.choice)
      (BinaryFractionalCore.start c
        (BinaryFractionalCore.parameters (BinaryFractionalCore.dimension c).1).delta
        (cached r.first.1.choice)).1=r.rest.state := by
  have h := replay_trace r.rest.trace (r.cache_empty hm hc)
  simpa [StartedResult.answers] using h

lemma link_answers_safe {c : Row m} {columns : Set (FractionalCover.Column m)}
    {p p' : Pending c columns} {s t : State m} {answer : Option (Answer m)}
    (h : Link c columns p s p' t answer) :
    ∀ a ∈ answer.toList, SafeChoice c columns a.choice := by
  cases h with
  | stopped => simp
  | cached => simp
  | fresh a s h =>
      intro b hb
      have he : b=a.1 := by simpa using hb
      subst b
      exact a.2

lemma trace_answers_safe {c : Row m} {columns : Set (FractionalCover.Column m)}
    {k : ℕ} {p p' : Pending c columns} {s t : State m} {answers : List (Answer m)}
    (h : Trace c columns k p s p' t answers) :
    ∀ a ∈ answers, SafeChoice c columns a.choice := by
  induction h with
  | zero => simp
  | succ head tail ih =>
      intro a ha
      rcases List.mem_append.mp ha with hh | ht
      · exact link_answers_safe head a hh
      · exact ih a ht

lemma input_answers_safe {c : Row m} {columns : Set (FractionalCover.Column m)}
    (r : InputResult c columns) : ∀ a ∈ r.answers, SafeChoice c columns a.choice := by
  intro a ha
  rcases List.mem_cons.mp ha with rfl | ha
  · exact r.first.2
  · exact trace_answers_safe r.rest.trace a ha


def sequenceRun (c : Row m) (delta : Fraction) (q : ℕ → Choice m) : ℕ → State m
  | 0 => (BinaryFractionalCore.start c delta (cached (q 0))).1
  | k+1 => (BinaryFractionalCore.step c (cached (q k)) (sequenceRun c delta q k)).1

theorem sequence_replay (c : Row m) (delta : Fraction) (q : ℕ → Choice m) (k : ℕ) :
    sequenceRun c delta q k = replayChoices c ((List.range k).map q)
      (BinaryFractionalCore.start c delta (cached (q 0))).1 := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [List.range_succ,List.map_append,replay_append]
      simp only [sequenceRun,replayChoices,ih,List.map_cons,List.map_nil]

theorem map_getD_range {A : Type} (xs : List A) (d : A) :
    (List.range xs.length).map (fun k => xs.getD k d)=xs := by
  apply List.ext_getElem (by simp)
  intro i hi hj
  simp [List.getD_eq_getElem?_getD,hj]

def choiceAt {c : Row m} {columns : Set (FractionalCover.Column m)}
    {delta : Fraction} {fuel : Bits} (r : StartedResult c columns delta fuel)
    (k : ℕ) : Choice m := (r.answers.getD k r.first.1).choice

lemma choiceAt_safe {c : Row m} {columns : Set (FractionalCover.Column m)}
    (r : InputResult c columns) (k : ℕ) : SafeChoice c columns (choiceAt r k) := by
  by_cases hk : k<r.answers.length
  · have h := input_answers_safe r r.answers[k] (List.getElem_mem hk)
    simpa only [choiceAt,List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hk,
      Option.getD_some] using h
  · have hnone : r.answers[k]?=none := List.getElem?_eq_none (by omega)
    simpa only [choiceAt,List.getD_eq_getElem?_getD,hnone,Option.getD_none] using r.first.2


theorem choiceAt_zero {c : Row m} {columns : Set (FractionalCover.Column m)}
    {delta : Fraction} {fuel : Bits} (r : StartedResult c columns delta fuel) :
    choiceAt r 0=r.first.1.choice := by simp [choiceAt,StartedResult.answers]

theorem choiceAt_list {c : Row m} {columns : Set (FractionalCover.Column m)}
    {delta : Fraction} {fuel : Bits} (r : StartedResult c columns delta fuel) :
    (List.range r.answers.length).map (choiceAt r)=r.answers.map Answer.choice := by
  calc
    _ = ((List.range r.answers.length).map (fun k => r.answers.getD k r.first.1)).map
        Answer.choice := by rw [List.map_map];rfl
    _ = _ := by rw [map_getD_range]

theorem sequence_stopped (c : Row m) (delta : Fraction) (q : ℕ → Choice m)
    (k d : ℕ) (h : (guard c (sequenceRun c delta q k)).1=true) :
    sequenceRun c delta q (k+d)=sequenceRun c delta q k := by
  induction d with
  | zero => simp
  | succ d ih =>
      rw [Nat.add_succ,sequenceRun,ih,cached_step_stopped c _ (q (k+d)) h]

theorem input_sequence {c : Row m} {columns : Set (FractionalCover.Column m)}
    (r : InputResult c columns) (hm : 0 < m)
    (hc : ∀ i, 0 < FractionalCover.value (capacities c) i) :
    sequenceRun c (BinaryFractionalCore.parameters (BinaryFractionalCore.dimension c).1).delta
      (choiceAt r) (FractionalCover.fuel m)=r.rest.state := by
  let delta := (BinaryFractionalCore.parameters (BinaryFractionalCore.dimension c).1).delta
  have hreplay : sequenceRun c delta (choiceAt r) r.answers.length=r.rest.state := by
    rw [sequence_replay,choiceAt_list,choiceAt_zero]
    exact input_replay r hm hc
  have hf := (BinaryFractionalCore.parameters_spec (BinaryFractionalCore.dimension c).1).1
  rw [(BinaryFractionalCore.dimension_spec c).1] at hf
  have hcount : r.rest.state.events.length ≤ FractionalCover.fuel m :=
    r.event_inputs.2.trans_eq hf
  rw [← r.calls_eq_events hm hc] at hcount
  have hstop : (guard c (sequenceRun c delta (choiceAt r) r.answers.length)).1=true := by
    rw [hreplay]
    exact (guard_spec c _).mpr (r.stopped hm hc)
  have hstable := sequence_stopped c delta (choiceAt r) r.answers.length
    (FractionalCover.fuel m-r.answers.length) hstop
  rw [show r.answers.length+(FractionalCover.fuel m-r.answers.length)=
    FractionalCover.fuel m by omega] at hstable
  exact hstable.trans hreplay

theorem sequence_value (c : Row m) (delta : Fraction) (q : ℕ → Choice m)
    (hd : decode delta=FractionalCoverRawCore.deltaCode m) (k : ℕ) :
    stateValue (sequenceRun c delta q k)=
      ApproximatePackingTrace.run (capacities c)
        (fun k _ => BinaryFractionalCore.decodeChoice (q k)) k := by
  induction k with
  | zero => exact cached_start_value c delta (q 0) hd
  | succ k ih =>
      simp only [sequenceRun,cached_step_value,ih,ApproximatePackingTrace.run]

def oracleAt {c : Row m} {columns : Set (FractionalCover.Column m)}
    (r : InputResult c columns) (k : ℕ) : FractionalCover.Oracle m :=
  fun _ => BinaryFractionalCore.decodeChoice (choiceAt r k)

/-- The complete retained state equals the pathwise run driven by its actual
answer sequence, padded only after stopping. No external transcript is assumed. -/
theorem input_pathwise {c : Row m} {columns : Set (FractionalCover.Column m)}
    (r : InputResult c columns) (hm : 0 < m)
    (hc : ∀ i, 0 < FractionalCover.value (capacities c) i) :
    stateValue r.rest.state=ApproximatePackingTrace.run (capacities c) (oracleAt r)
      (FractionalCover.fuel m) := by
  have hd := (BinaryFractionalCore.parameters_spec (BinaryFractionalCore.dimension c).1).2
  rw [(BinaryFractionalCore.dimension_spec c).1] at hd
  rw [← input_sequence r hm hc]
  exact sequence_value c _ (choiceAt r) hd (FractionalCover.fuel m)

/-- This budget is imposed only on choices actually used before the retained
answer list ends. It is proof-side and is never a computable alpha test. The
provider's conditional good-event theorem must establish it at the same query
rows; it is not inferred from the provider's failure flag. -/
def GoodBudget {c : Row m} {columns : Set (FractionalCover.Column m)}
    (r : InputResult c columns) (α : ℝ) : Prop :=
  ∀ k<r.answers.length,
    let s := ApproximatePackingTrace.run (capacities c) (oracleAt r) k
    FractionalCover.objective (capacities c) s.weights < 1 →
      (FractionalCover.length s.weights (BinaryFractionalCore.decodeChoice (choiceAt r k)).column : ℝ)
        ≤ α*(FractionalCover.objective (capacities c) s.weights : ℝ)

lemma pathwise_stopped_after_answers {c : Row m} {columns : Set (FractionalCover.Column m)}
    (r : InputResult c columns) (hm : 0 < m)
    (hc : ∀ i, 0 < FractionalCover.value (capacities c) i) (k : ℕ)
    (hk : r.answers.length ≤ k) :
    1 ≤ FractionalCover.objective (capacities c)
      (ApproximatePackingTrace.run (capacities c) (oracleAt r) k).weights := by
  let delta := (BinaryFractionalCore.parameters (BinaryFractionalCore.dimension c).1).delta
  have hd := (BinaryFractionalCore.parameters_spec (BinaryFractionalCore.dimension c).1).2
  rw [(BinaryFractionalCore.dimension_spec c).1] at hd
  have hreplay : sequenceRun c delta (choiceAt r) r.answers.length=r.rest.state := by
    rw [sequence_replay,choiceAt_list,choiceAt_zero]
    exact input_replay r hm hc
  have hs : (guard c (sequenceRun c delta (choiceAt r) r.answers.length)).1=true := by
    rw [hreplay]
    exact (guard_spec c _).mpr (r.stopped hm hc)
  have he := sequence_stopped c delta (choiceAt r) r.answers.length
    (k-r.answers.length) hs
  rw [Nat.add_sub_of_le hk,hreplay] at he
  have hv := sequence_value c delta (choiceAt r) hd k
  rw [he] at hv
  change 1 ≤ FractionalCover.objective (capacities c)
    (ApproximatePackingTrace.run (capacities c) (fun j _ =>
      BinaryFractionalCore.decodeChoice (choiceAt r j)) k).weights
  rw [← hv]
  exact r.stopped hm hc

/-- Approximate choice correctness, without an exact-minimum-column premise. -/
theorem choicesCorrect {c : Row m} {columns : Set (FractionalCover.Column m)}
    (r : InputResult c columns) (hm : 0 < m)
    (hc : ∀ i, 0 < FractionalCover.value (capacities c) i)
    (α : ℝ) (hb : GoodBudget r α) :
    ApproximatePackingTrace.ChoicesCorrect (capacities c) columns (oracleAt r) α := by
  constructor
  · intro k _
    exact (choiceAt_safe r k).1
  · intro k _
    exact (choiceAt_safe r k).2.1
  · intro k _
    exact (choiceAt_safe r k).2.2
  · intro k ha
    have hk : k<r.answers.length := by
      by_contra hn
      exact (not_lt_of_ge (pathwise_stopped_after_answers r hm hc k (by omega))) ha
    exact hb k hk ha

/-- The marginal denominator is proved positive for the actual retained state.
This theorem is conditional only on the reached cost budgets; structural
validity, positive amounts and stopping are supplied by the execution itself. -/
theorem retained_marginal_le {c : Row m} {columns : Set (FractionalCover.Column m)}
    (r : InputResult c columns) (hm : 0 < m)
    (hc : ∀ i, 0 < FractionalCover.value (capacities c) i)
    {α : ℝ} (hα : 0<α) (hb : GoodBudget r α) (i : Fin m) :
    0 < FractionalCover.traceTotal (stateValue r.rest.state).events ∧
      (FractionalCover.traceLoad (stateValue r.rest.state).events i : ℝ) /
        (FractionalCover.traceTotal (stateValue r.rest.state).events : ℝ) ≤
          3*α*(FractionalCover.value (capacities c) i : ℝ) := by
  rw [input_pathwise r hm hc]
  exact ApproximatePackingTrace.trace_marginal_le (capacities c) columns (oracleAt r)
    hm hc hα (choicesCorrect r hm hc α hb) i

end DirectedFlowCutGap.BinaryApproximatePackingTrace
