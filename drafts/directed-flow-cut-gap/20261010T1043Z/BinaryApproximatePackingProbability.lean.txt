import DirectedFlowCutGap.BinaryApproximatePackingZeros
import DirectedFlowCutGap.WeightedMixtureBound
import Mathlib.Data.List.GetD

/-!
# Adaptive query quality for the actual cached packing controller

This is an uncompiled development draft. Its direct frozen dependency hashes
and remaining verification gates are recorded in the companion contract.

The probability space is the actual `runFromM` / `runM` / `solveInputM` law.
The first provider answer is shared between initialization and the first active
step, and later queries occur only at active reached rows. A replay predicate
checks cost quality at those same rows. Its bad mass is bounded by induction on
the binary fuel, using PMF bind on arbitrary dependent histories. There is no
finite-history assumption, independence premise, or conditioning shortcut.

Cost quality and `Answer.failed` are distinct. The final specialization uses
original input weights, even when the controller uses positive auxiliary
capacities. Alpha is only a proof parameter and need not be at least one.
-/
namespace DirectedFlowCutGap.BinaryApproximatePackingProbability

open BinaryApproximatePacking BinaryApproximatePackingTrace
open BinaryApproximatePackingZeros BinaryArithmetic BinaryFractionalRows BinaryRational
open scoped ENNReal

noncomputable section

variable {m : ℕ}

/-- Query quality, checked before consuming each replayed choice. -/
def ReplayGood (c : Row m) (good : Row m → Choice m → Prop) :
    State m → List (Choice m) → Prop
  | _, [] => True
  | s, q::qs => good s.weights q ∧
      ReplayGood c good (BinaryFractionalCore.step c (cached q) s).1 qs

def PendingGood {c : Row m} {columns : Set (FractionalCover.Column m)}
    (good : Row m → Choice m → Prop) (p : Pending c columns) (s : State m) : Prop :=
  ∀ q ∈ p.toList, good s.weights q.1

/-- Only a genuinely fresh answer contributes a new quality obligation. -/
def RoundGood {c : Row m} {columns : Set (FractionalCover.Column m)}
    {p : Pending c columns} (good : Row m → Choice m → Prop) (s : State m)
    (r : Round c columns p s) : Prop :=
  ∀ a ∈ r.answer.toList, good s.weights a.choice

def RunGood {c : Row m} {columns : Set (FractionalCover.Column m)}
    {p : Pending c columns} {s : State m} {k : ℕ}
    (good : Row m → Choice m → Prop) (r : RunResult c columns p s k) : Prop :=
  ReplayGood c good s (p.toList.map Subtype.val ++ r.answers.map Answer.choice)

def StartedGood {c : Row m} {columns : Set (FractionalCover.Column m)}
    {delta : Fraction} {fuel : Bits} (good : Row m → Choice m → Prop)
    (r : StartedResult c columns delta fuel) : Prop :=
  ReplayGood c good (BinaryFractionalCore.start c delta (cached r.first.1.choice)).1
    (r.answers.map Answer.choice)

lemma pendingGood_nil {c : Row m} {columns : Set (FractionalCover.Column m)}
    (good : Row m → Choice m → Prop) (s : State m) :
    PendingGood (c := c) (columns := columns) good none s := by
  simp [PendingGood]

lemma replayGood_pending {c : Row m} {columns : Set (FractionalCover.Column m)}
    (good : Row m → Choice m → Prop) (p : Pending c columns) (s : State m)
    (hp : PendingGood good p s) :
    ReplayGood c good s (p.toList.map Subtype.val) := by
  cases p with
  | none => trivial
  | some q => exact ⟨hp q (by simp), trivial⟩

lemma link_pending_good {c : Row m} {columns : Set (FractionalCover.Column m)}
    {p p' : Pending c columns} {s t : State m} {a : Option (Answer m)}
    (h : Link c columns p s p' t a) (good : Row m → Choice m → Prop)
    (hp : PendingGood good p s) : PendingGood good p' t := by
  cases h with
  | stopped => exact hp
  | cached => exact pendingGood_nil _ _
  | fresh => exact pendingGood_nil _ _

lemma link_replay_good {c : Row m} {columns : Set (FractionalCover.Column m)}
    {p p' : Pending c columns} {s t : State m} {a : Option (Answer m)}
    (h : Link c columns p s p' t a) (good : Row m → Choice m → Prop)
    (hp : PendingGood good p s)
    (ha : ∀ b ∈ a.toList, good s.weights b.choice)
    (answers : List (Answer m))
    (ht : ReplayGood c good t (p'.toList.map Subtype.val ++ answers.map Answer.choice)) :
    ReplayGood c good s
      (p.toList.map Subtype.val ++ (a.toList ++ answers).map Answer.choice) := by
  cases h with
  | stopped => simpa using ht
  | cached q s h =>
      exact ⟨hp q (by simp), by simpa using ht⟩
  | fresh a s h =>
      exact ⟨ha a.1 (by simp), by simpa using ht⟩

/-- Deterministic postprocessing cannot enlarge failure when it preserves good
outputs. Neither the input nor the output type needs a finite instance. -/
lemma bind_pure_bad_le {A B : Type*} (p : PMF A) (f : A → B)
    (good : A → Prop) (good' : B → Prop)
    (hf : ∀ a, good a → good' (f a)) :
    (p.bind (fun a => PMF.pure (f a))).toOuterMeasure {b | ¬ good' b} ≤
      p.toOuterMeasure {a | ¬ good a} := by
  change (p.map f).toOuterMeasure {b | ¬ good' b} ≤ _
  rw [PMF.toOuterMeasure_map_apply]
  apply p.toOuterMeasure.mono
  intro a ha hga
  exact ha (hf a hga)

/-- A stopped or cached round has no new bad-query mass. Only the actual fresh
branch uses the one-query hypothesis at `s.weights`. -/
theorem advance_bad_le (c : Row m) (columns : Set (FractionalCover.Column m))
    (draw : Oracle PMF c columns) (good : Row m → Choice m → Prop)
    (ε : ℝ≥0∞)
    (hdraw : ∀ y, (draw y).toOuterMeasure {a | ¬ good y a.1.choice} ≤ ε)
    (p : Pending c columns) (s : State m) :
    (advance c columns draw p s).toOuterMeasure {r | ¬ RoundGood good s r} ≤ ε := by
  classical
  by_cases hs : (guard c s).1 = true
  · simp only [advance, hs, dite_true]
    change (PMF.pure _).toOuterMeasure _ ≤ ε
    simp [RoundGood]
  · cases p with
    | some q =>
        simp only [advance, hs]
        change (PMF.pure _).toOuterMeasure _ ≤ ε
        simp [RoundGood]
    | none =>
        simp only [advance, hs]
        apply (bind_pure_bad_le (draw s.weights) _
          (fun a => good s.weights a.1.choice) _ ?_).trans (hdraw s.weights)
        intro a ha
        simpa [RoundGood] using ha

/-- Each remaining scan may contribute at most epsilon. The induction follows
the actual binary predecessor and actual PMF bind, at arbitrary reached states.
The pending choice was already drawn, so its quality is an explicit invariant.
-/
theorem runFromM_bad_le (c : Row m) (columns : Set (FractionalCover.Column m))
    (draw : Oracle PMF c columns) (good : Row m → Choice m → Prop)
    (ε : ℝ≥0∞)
    (hdraw : ∀ y, (draw y).toOuterMeasure {a | ¬ good y a.1.choice} ≤ ε)
    (fuel : Bits) (p : Pending c columns) (s : State m)
    (hp : PendingGood good p s) :
    (runFromM c columns draw fuel p s).toOuterMeasure {r | ¬ RunGood good r} ≤
      (value fuel : ℝ≥0∞) * ε := by
  classical
  rw [runFromM]
  dsimp only
  split
  · rename_i hz
    have hg := replayGood_pending good p s hp
    change (PMF.pure _).toOuterMeasure _ ≤ _
    rw [PMF.toOuterMeasure_pure_apply]
    simp only [Set.mem_ofPred_eq, RunGood, List.map_nil, List.append_nil]
    rw [ite_eq_right (not_not.mpr hg)]
    exact bot_le
  · rename_i hz
    have hpos : 0 < value fuel := Nat.pos_of_ne_zero
      (fun h => hz ((isZero_spec fuel).1.mpr h))
    have hpred := (predecessor_spec fuel).1
    have hf : value fuel = value (predecessor fuel).1 + 1 := by omega
    refine (WeightedMixtureBound.bind_event_le (advance c columns draw p s) _
      (RoundGood good s) _ ((value (predecessor fuel).1 : ℝ≥0∞) * ε) ?_).trans ?_
    · intro next _ hn
      have hp' := link_pending_good next.link good hp
      have ih := runFromM_bad_le c columns draw good ε hdraw
        (predecessor fuel).1 next.pending next.state hp'
      apply (bind_pure_bad_le
        (runFromM c columns draw (predecessor fuel).1 next.pending next.state) _
        (RunGood good) _ ?_).trans ih
      intro rest hr
      exact link_replay_good next.link good hp hn rest.answers hr
    · calc
        (value (predecessor fuel).1 : ℝ≥0∞) * ε +
            (advance c columns draw p s).toOuterMeasure {r | ¬ RoundGood good s r}
            ≤ (value (predecessor fuel).1 : ℝ≥0∞) * ε + ε :=
          add_le_add le_rfl (advance_bad_le c columns draw good ε hdraw p s)
        _ = (value fuel : ℝ≥0∞) * ε := by rw [hf]; simp [Nat.cast_add, add_mul]
termination_by value fuel
decreasing_by
  have hz : ¬ (isZero fuel).1 = true := by assumption
  have _hpos : 0 < value fuel := Nat.pos_of_ne_zero
    (fun h => hz ((isZero_spec fuel).1.mpr h))
  rw [(predecessor_spec fuel).1]
  omega

/-- Startup adds exactly one possible bad draw. Its answer is then supplied as
the cache to the existing worker rather than sampled a second time. -/
theorem runM_bad_le (c : Row m) (columns : Set (FractionalCover.Column m))
    (draw : Oracle PMF c columns) (good : Row m → Choice m → Prop)
    (ε : ℝ≥0∞)
    (hdraw : ∀ y, (draw y).toOuterMeasure {a | ¬ good y a.1.choice} ≤ ε)
    (delta : Fraction) (fuel : Bits) :
    (runM c columns draw delta fuel).toOuterMeasure {r | ¬ StartedGood good r} ≤
      ((value fuel + 1 : ℕ) : ℝ≥0∞) * ε := by
  classical
  rw [runM]
  dsimp only
  refine (WeightedMixtureBound.bind_event_le (draw (initial c delta).1) _
    (fun a => good (initial c delta).1 a.1.choice) _
    ((value fuel : ℝ≥0∞) * ε) ?_).trans ?_
  · intro first _ hf
    have hp : PendingGood good (some ⟨first.1.choice,first.2⟩)
        (BinaryFractionalCore.start c delta (cached first.1.choice)).1 := by
      simpa [PendingGood, BinaryFractionalCore.start] using hf
    have ih := runFromM_bad_le c columns draw good ε hdraw fuel _ _ hp
    apply (bind_pure_bad_le _ _ (RunGood good) _ ?_).trans ih
    intro rest hr
    simpa only [RunGood, StartedGood, StartedResult.answers,
      Option.toList_some, List.map_cons, List.map_nil, List.cons_append,
      List.nil_append] using hr
  · calc
      (value fuel : ℝ≥0∞) * ε +
          (draw (initial c delta).1).toOuterMeasure
            {a | ¬ good (initial c delta).1 a.1.choice}
          ≤ (value fuel : ℝ≥0∞) * ε + ε := add_le_add le_rfl (hdraw _)
      _ = ((value fuel + 1 : ℕ) : ℝ≥0∞) * ε := by simp [Nat.cast_add, add_mul]

set_option maxHeartbeats 800000 in
theorem solveInputM_bad_le (c : Row m) (columns : Set (FractionalCover.Column m))
    (draw : Oracle PMF c columns) (good : Row m → Choice m → Prop)
    (ε : ℝ≥0∞)
    (hdraw : ∀ y, (draw y).toOuterMeasure {a | ¬ good y a.1.choice} ≤ ε) :
    (solveInputM c columns draw).toOuterMeasure {r | ¬ StartedGood good r} ≤
      ((3*m^2 + 1 : ℕ) : ℝ≥0∞) * ε := by
  classical
  have hf := (BinaryFractionalCore.parameters_spec (BinaryFractionalCore.dimension c).1).1
  rw [(BinaryFractionalCore.dimension_spec c).1] at hf
  have hr := runM_bad_le c columns draw good ε hdraw
    (BinaryFractionalCore.parameters (BinaryFractionalCore.dimension c).1).delta
    (BinaryFractionalCore.parameters (BinaryFractionalCore.dimension c).1).fuel
  rw [hf] at hr
  change _ ≤ ((FractionalCover.fuel m + 1 : ℕ) : ℝ≥0∞) * ε
  rw [solveInputM]
  refine (bind_pure_bad_le
    (runM c columns draw
      (BinaryFractionalCore.parameters (BinaryFractionalCore.dimension c).1).delta
      (BinaryFractionalCore.parameters (BinaryFractionalCore.dimension c).1).fuel)
    (fun r => {r with operations := (BinaryFractionalCore.dimension c).2 +
      (BinaryFractionalCore.parameters (BinaryFractionalCore.dimension c).1).operations +
      r.operations + 8})
    (StartedGood good) (StartedGood good) ?_).trans hr
  intro r hg
  exact hg

lemma replayGood_getD (c : Row m) (good : Row m → Choice m → Prop)
    (s : State m) (qs : List (Choice m)) (h : ReplayGood c good s qs)
    (d : Choice m) (k : ℕ) (hk : k < qs.length) :
    good (replayChoices c (qs.take k) s).weights (qs.getD k d) := by
  induction qs generalizing s k with
  | nil => simp at hk
  | cons q qs ih =>
      cases k with
      | zero => simpa [ReplayGood, replayChoices] using h.1
      | succ k =>
          have ht := ih (BinaryFractionalCore.step c (cached q) s).1 h.2 k (by simpa using hk)
          simpa only [List.take_succ_cons, replayChoices, List.getD_cons_succ] using ht

lemma map_getD_range_take {A : Type*} (xs : List A) (d : A) (k : ℕ)
    (hk : k ≤ xs.length) :
    (List.range k).map (fun j => xs.getD j d) = xs.take k := by
  apply List.ext_getElem (by simp [hk])
  intro i hi hj
  have hik : i < k := by simpa only [List.length_map, List.length_range] using hi
  have hix : i < xs.length := lt_of_lt_of_le hik hk
  simp [List.getD_eq_getElem?_getD, hix]

/-- The row used by the replay quality test is the complete reconstructed
controller state at the corresponding actual retained answer index. -/
theorem startedGood_query {c : Row m} {columns : Set (FractionalCover.Column m)}
    {delta : Fraction} {fuel : Bits} (r : StartedResult c columns delta fuel)
    (good : Row m → Choice m → Prop) (hg : StartedGood good r)
    (k : ℕ) (hk : k < r.answers.length) :
    good (sequenceRun c delta (choiceAt r) k).weights (choiceAt r k) := by
  have hp : (List.range k).map (choiceAt r) = (r.answers.map Answer.choice).take k := by
    calc
      _ = ((List.range k).map (fun j => r.answers.getD j r.first.1)).map
          Answer.choice := by rw [List.map_map]; rfl
      _ = (r.answers.take k).map Answer.choice := by
        rw [map_getD_range_take r.answers r.first.1 k hk.le]
      _ = _ := by rw [List.map_take]
  have h := replayGood_getD c good _ (r.answers.map Answer.choice) hg
    r.first.1.choice k (by simpa using hk)
  rw [List.getD_map] at h
  rw [sequence_replay, hp, choiceAt_zero]
  exact h

/-- The oracle budget evaluates the original capacities and the exact queried
binary row. It is independent of the provider's physical failure flag. -/
def OriginalQuality (w : Row m) (α : ℝ) (y : Row m) (q : Choice m) : Prop :=
  (FractionalCover.length (capacities y) (BinaryFractionalCore.decodeChoice q).column : ℝ)
    ≤ α * (FractionalCover.objective (capacities w) (capacities y) : ℝ)

theorem startedGood_originalBudget {w : Row m} {columns : Set (FractionalCover.Column m)}
    (r : InputResult (auxiliary w) (zeroFreeColumns w columns)) (α : ℝ)
    (hg : StartedGood (OriginalQuality w α) r) : OriginalBudget r α := by
  intro k hk
  dsimp only
  intro _ha
  have h := startedGood_query r (OriginalQuality w α) hg k hk
  have hd := (BinaryFractionalCore.parameters_spec
    (BinaryFractionalCore.dimension (auxiliary w)).1).2
  rw [(BinaryFractionalCore.dimension_spec (auxiliary w)).1] at hd
  have hv := sequence_value (auxiliary w) _ (choiceAt r) hd k
  change (FractionalCover.length
      (stateValue (sequenceRun (auxiliary w) _ (choiceAt r) k)).weights
      (BinaryFractionalCore.decodeChoice (choiceAt r k)).column : ℝ) ≤
    α * (FractionalCover.objective (capacities w)
      (stateValue (sequenceRun (auxiliary w) _ (choiceAt r) k)).weights : ℝ) at h
  rw [hv] at h
  unfold BinaryApproximatePackingTrace.oracleAt
  exact h

/-- The bad original-weight budget mass of the actual controller. No extra
condition on alpha, on finite histories, or on exact minimum cut cost is used. -/
theorem originalBudget_failure_le (w : Row m)
    (columns : Set (FractionalCover.Column m))
    (draw : Oracle PMF (auxiliary w) (zeroFreeColumns w columns)) (α : ℝ)
    (ε : ℝ≥0∞)
    (hdraw : ∀ y, (draw y).toOuterMeasure {a | ¬ OriginalQuality w α y a.1.choice} ≤ ε) :
    (solveInputM (auxiliary w) (zeroFreeColumns w columns) draw).toOuterMeasure
        {r | ¬ OriginalBudget r α} ≤ ((3*m^2 + 1 : ℕ) : ℝ≥0∞) * ε := by
  apply le_trans _ (solveInputM_bad_le (auxiliary w) (zeroFreeColumns w columns)
    draw (OriginalQuality w α) ε hdraw)
  apply (solveInputM (auxiliary w) (zeroFreeColumns w columns) draw).toOuterMeasure.mono
  intro r hr hg
  exact hr (startedGood_originalBudget r α hg)

/-- Real-valued interface for the unconditional weighted-sampler composition. -/
theorem originalBudget_failure_toReal_le (w : Row m)
    (columns : Set (FractionalCover.Column m))
    (draw : Oracle PMF (auxiliary w) (zeroFreeColumns w columns)) (α ε : ℝ)
    (hε : 0 ≤ ε)
    (hdraw : ∀ y, ((draw y).toOuterMeasure
      {a | ¬ OriginalQuality w α y a.1.choice}).toReal ≤ ε) :
    ((solveInputM (auxiliary w) (zeroFreeColumns w columns) draw).toOuterMeasure
        {r | ¬ OriginalBudget r α}).toReal ≤ (3*m^2 + 1 : ℕ) * ε := by
  have hd : ∀ y, (draw y).toOuterMeasure
      {a | ¬ OriginalQuality w α y a.1.choice} ≤ ENNReal.ofReal ε := by
    intro y
    have hfinite : (draw y).toOuterMeasure
        {a | ¬ OriginalQuality w α y a.1.choice} ≠ ⊤ :=
      (lt_of_le_of_lt (WeightedMixtureBound.event_le_one (draw y) _) (by simp)).ne
    have h := ENNReal.ofReal_le_ofReal (hdraw y)
    rwa [ENNReal.ofReal_toReal hfinite] at h
  have h := originalBudget_failure_le w columns draw α (ENNReal.ofReal ε) hd
  have hb : ((3*m^2 + 1 : ℕ) : ℝ≥0∞) * ENNReal.ofReal ε =
      ENNReal.ofReal ((3*m^2 + 1 : ℕ) * ε) := by
    rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_natCast]
  rw [hb] at h
  exact ENNReal.toReal_le_of_le_ofReal (by positivity) h

end
end DirectedFlowCutGap.BinaryApproximatePackingProbability
