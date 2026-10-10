import DirectedFlowCutGap.BinaryFractionalStepCost
import DirectedFlowCutGap.ApproximatePackingTrace

/-!
# Cached-choice monadic packing on the retained binary state

The first actual oracle answer is shared by initialization and the first active
step. Subsequent active states make fresh monadic calls; stopped states make no
calls but continue every binary-fuel guard scan. The wrapper deliberately pays
for its preview initial row and for the extra guard on active rounds before
reusing the frozen Core.step. Natural counters are ghost instrumentation.

Returned certificates are proposition-valued and erase. They record the same
states, cache transitions and actual fresh-answer list as the executable body.
Structural cut validity and attained bottlenecks hold independently of any
alpha-cost budget; alpha never appears in executable data or guards. A concrete
stochastic cut provider and its all-branch implementation cost remain a join.
-/
namespace DirectedFlowCutGap.BinaryApproximatePacking
open BinaryArithmetic BinaryRational BinaryFractionalRows

abbrev State := BinaryFractionalCore.State
abbrev Choice := BinaryFractionalCore.Choice
abbrev Event := BinaryFractionalCore.Event

variable {m : ℕ}

def capacities (c : Row m) : FractionalCover.Row m :=
  FractionalCoverRawCore.decodeRow (BinaryFractionalRows.decodeRow c)

def stateValue (s : State m) : FractionalCover.State m :=
  FractionalCoverRawCore.decodeState (BinaryFractionalCore.decodeState s)

/-- These are structural guarantees, with no cost-quality hypothesis. -/
def SafeChoice (c : Row m) (columns : Set (FractionalCover.Column m))
    (q : Choice m) : Prop :=
  (BinaryFractionalCore.decodeChoice q).column ∈ columns ∧
  q.bottleneck ∈ (BinaryFractionalCore.decodeChoice q).column ∧
  ∀ i ∈ (BinaryFractionalCore.decodeChoice q).column,
    FractionalCover.value (capacities c) q.bottleneck ≤
      FractionalCover.value (capacities c) i

/-- The actual provider's metadata is retained, including a failure flag.
A failure flag does not discard structural validity of its fallback choice. -/
structure Answer (m : ℕ) where
  choice : Choice m
  operations : ℕ
  failed : Bool
  trials : Bits
  consumed : Bits

abbrev SafeAnswer (c : Row m) (columns : Set (FractionalCover.Column m)) :=
  {a : Answer m // SafeChoice c columns a.choice}

abbrev Pending (c : Row m) (columns : Set (FractionalCover.Column m)) :=
  Option {q : Choice m // SafeChoice c columns q}

abbrev Oracle (M : Type → Type) (c : Row m)
    (columns : Set (FractionalCover.Column m)) := Row m → M (SafeAnswer c columns)

/-- A fixed retained-record callback. The stochastic provider was already called
outside this callback. Its one structural return operation is not an opaque
oracle execution charge. Representation overhead remains a separate join. -/
def cached (q : Choice m) : BinaryFractionalCore.Oracle m := fun _ => (q,1)

def guard (c : Row m) (s : State m) : Bool × ℕ :=
  let d := objective c s.weights
  let stop := BinaryRational.le one d.1
  (stop.1,d.2+stop.2+4)

theorem cached_step_stopped (c : Row m) (s : State m) (q : Choice m)
    (h : (guard c s).1=true) :
    BinaryFractionalCore.step c (cached q) s = (s,(guard c s).2) := by
  unfold BinaryFractionalCore.step guard at *
  dsimp only at *
  simp only [h,ite_true]

theorem cached_step_events (c : Row m) (s : State m) (q : Choice m)
    (h : (guard c s).1=false) :
    (BinaryFractionalCore.step c (cached q) s).1.events =
      ⟨q,get c q.bottleneck⟩::s.events := by
  unfold BinaryFractionalCore.step guard at *
  dsimp only [cached] at *
  simp only [h,Bool.false_eq_true,ite_false]

/-- One actual round, recording exactly whether a fresh provider answer occurs. -/
inductive Link (c : Row m) (columns : Set (FractionalCover.Column m)) :
    Pending c columns → State m → Pending c columns → State m → Option (Answer m) → Prop
  | stopped (p : Pending c columns) (s : State m) (h : (guard c s).1=true) :
      Link c columns p s p s none
  | cached (q : {q : Choice m // SafeChoice c columns q}) (s : State m)
      (h : (guard c s).1=false) :
      Link c columns (some q) s none
        (BinaryFractionalCore.step c (BinaryApproximatePacking.cached q.1) s).1 none
  | fresh (a : SafeAnswer c columns) (s : State m) (h : (guard c s).1=false) :
      Link c columns none s none
        (BinaryFractionalCore.step c (BinaryApproximatePacking.cached a.1.choice) s).1 (some a.1)

inductive Trace (c : Row m) (columns : Set (FractionalCover.Column m)) :
    ℕ → Pending c columns → State m → Pending c columns → State m → List (Answer m) → Prop
  | zero (p : Pending c columns) (s : State m) : Trace c columns 0 p s p s []
  | succ {k : ℕ} {p p' p'' : Pending c columns} {s t u : State m}
      {answer : Option (Answer m)} {answers : List (Answer m)}
      (head : Link c columns p s p' t answer)
      (tail : Trace c columns k p' t p'' u answers) :
      Trace c columns (k+1) p s p'' u (answer.toList++answers)

structure Round (c : Row m) (columns : Set (FractionalCover.Column m))
    (p : Pending c columns) (s : State m) where
  state : State m
  pending : Pending c columns
  answer : Option (Answer m)
  operations : ℕ
  guardTests : ℕ
  link : Link c columns p s pending state answer
  guardTests_le : guardTests ≤ 2
  guardTests_balance : guardTests+s.events.length=1+state.events.length

/-- The outer guard avoids a fresh query after stopping. On active rounds its
cost is retained in addition to Core.step's own guard cost. -/
def advance {M : Type → Type} [Monad M] (c : Row m)
    (columns : Set (FractionalCover.Column m)) (draw : Oracle M c columns)
    (p : Pending c columns) (s : State m) : M (Round c columns p s) := do
  let g := guard c s
  if h : g.1=true then
    pure ⟨s,p,none,g.2,1,Link.stopped p s h,by decide,rfl⟩
  else
    have hactive : (guard c s).1=false := Bool.eq_false_iff.mpr h
    match hp : p with
    | some q =>
        let r := BinaryFractionalCore.step c (cached q.1) s
        pure ⟨r.1,none,none,g.2+r.2+4,2,
          by simpa only [hp] using Link.cached q s hactive,by decide,by
          dsimp only [r]
          rw [cached_step_events c s q.1 hactive]
          simp only [List.length_cons]
          omega⟩
    | none =>
        let a ← draw s.weights
        let r := BinaryFractionalCore.step c (cached a.1.choice) s
        pure ⟨r.1,none,some a.1,g.2+a.1.operations+r.2+8,2,
          by simpa only [hp] using Link.fresh a s hactive,by decide,by
            dsimp only [r]
            rw [cached_step_events c s a.1.choice hactive]
            simp only [List.length_cons]
            omega⟩

structure RunResult (c : Row m) (columns : Set (FractionalCover.Column m))
    (p : Pending c columns) (s : State m) (k : ℕ) where
  state : State m
  pending : Pending c columns
  answers : List (Answer m)
  operations : ℕ
  stopTests : ℕ
  guardTests : ℕ
  trace : Trace c columns k p s pending state answers
  stopTests_eq : stopTests=k
  guardTests_le : guardTests ≤ 2*k
  guardTests_balance : guardTests+s.events.length=k+state.events.length

/-- Actual binary fuel controls every remaining scan, including stopped scans. -/
def runFromM {M : Type → Type} [Monad M] (c : Row m)
    (columns : Set (FractionalCover.Column m)) (draw : Oracle M c columns)
    (fuel : Bits) (p : Pending c columns) (s : State m) :
    M (RunResult c columns p s (value fuel)) := do
  let z := BinaryArithmetic.isZero fuel
  if hz : z.1=true then
    have hv : value fuel=0 := (isZero_spec fuel).1.mp hz
    pure ⟨s,p,[],z.2+4,0,0,by simpa only [hv] using Trace.zero p s,hv.symm,by omega,by omega⟩
  else
    let pred := predecessor fuel
    have hpos : 0<value fuel := Nat.pos_of_ne_zero
      (fun h => hz ((isZero_spec fuel).1.mpr h))
    have hpred := (predecessor_spec fuel).1
    have hf : value fuel=value pred.1+1 := by dsimp [pred];omega
    let next ← advance c columns draw p s
    let rest ← runFromM c columns draw pred.1 next.pending next.state
    pure ⟨rest.state,rest.pending,next.answer.toList++rest.answers,
      z.2+pred.2+next.operations+rest.operations+8,rest.stopTests+1,
      next.guardTests+rest.guardTests,
      by simpa only [hf] using Trace.succ next.link rest.trace,
      by rw [rest.stopTests_eq];omega,
      by have ha := next.guardTests_le;have hb := rest.guardTests_le;omega,
      by have ha := next.guardTests_balance;have hb := rest.guardTests_balance;omega⟩
termination_by value fuel
decreasing_by
  have _hpos : 0<value fuel := Nat.pos_of_ne_zero
    (fun h => hz ((isZero_spec fuel).1.mpr h))
  rw [(predecessor_spec fuel).1]
  omega

structure StartedResult (c : Row m) (columns : Set (FractionalCover.Column m))
    (delta : Fraction) (fuel : Bits) where
  first : SafeAnswer c columns
  rest : RunResult c columns (some ⟨first.1.choice,first.2⟩)
    (BinaryFractionalCore.start c delta (cached first.1.choice)).1 (value fuel)
  operations : ℕ

/-- The chronological list includes the one startup query. The first active
step consumes its cached choice and does not issue that query again. -/
def StartedResult.answers {c : Row m} {columns : Set (FractionalCover.Column m)}
    {delta : Fraction} {fuel : Bits} (r : StartedResult c columns delta fuel) : List (Answer m) :=
  r.first.1::r.rest.answers

/-- Preview initialization is a real additional computation and is charged. -/
def runM {M : Type → Type} [Monad M] (c : Row m)
    (columns : Set (FractionalCover.Column m)) (draw : Oracle M c columns)
    (delta : Fraction) (fuel : Bits) : M (StartedResult c columns delta fuel) := do
  let preview := initial c delta
  let first ← draw preview.1
  let start := BinaryFractionalCore.start c delta (cached first.1.choice)
  let rest ← runFromM c columns draw fuel (some ⟨first.1.choice,first.2⟩) start.1
  pure ⟨first,rest,preview.2+first.1.operations+start.2+rest.operations+12⟩

abbrev InputResult (c : Row m) (columns : Set (FractionalCover.Column m)) :=
  let p := BinaryFractionalCore.parameters (BinaryFractionalCore.dimension c).1
  StartedResult c columns p.delta p.fuel

def solveInputM {M : Type → Type} [Monad M] (c : Row m)
    (columns : Set (FractionalCover.Column m)) (draw : Oracle M c columns) :
    M (InputResult c columns) := do
  let dim := BinaryFractionalCore.dimension c
  let p := BinaryFractionalCore.parameters dim.1
  let r ← runM c columns draw p.delta p.fuel
  pure {r with operations := dim.2+p.operations+r.operations+8}

/-- A literal monadic equation exposes the one initial provider call. All other
provider calls are inside the cache-aware worker, at reached active states. -/
theorem runM_equation {M : Type → Type} [Monad M] (c : Row m)
    (columns : Set (FractionalCover.Column m)) (draw : Oracle M c columns)
    (delta : Fraction) (fuel : Bits) :
    runM c columns draw delta fuel = (do
      let preview := initial c delta
      let first ← draw preview.1
      let start := BinaryFractionalCore.start c delta (cached first.1.choice)
      let rest ← runFromM c columns draw fuel (some ⟨first.1.choice,first.2⟩) start.1
      pure ⟨first,rest,preview.2+first.1.operations+start.2+rest.operations+12⟩) := rfl

theorem Link.event_inputs {c : Row m} {columns : Set (FractionalCover.Column m)}
    {p p' : Pending c columns} {s t : State m} {answer : Option (Answer m)}
    (h : Link c columns p s p' t answer) (hs : BinaryFractionalWidths.EventInputs c s) :
    BinaryFractionalWidths.EventInputs c t ∧ t.events.length ≤ s.events.length+1 := by
  cases h with
  | stopped => exact ⟨hs,Nat.le_succ _⟩
  | cached q s h =>
      exact BinaryFractionalWidths.step_events c (BinaryApproximatePacking.cached q.1) s hs
  | fresh a s h =>
      exact BinaryFractionalWidths.step_events c (BinaryApproximatePacking.cached a.1.choice) s hs

theorem Trace.event_inputs {c : Row m} {columns : Set (FractionalCover.Column m)}
    {k : ℕ} {p p' : Pending c columns} {s t : State m} {answers : List (Answer m)}
    (h : Trace c columns k p s p' t answers) (hs : BinaryFractionalWidths.EventInputs c s) :
    BinaryFractionalWidths.EventInputs c t ∧ t.events.length ≤ s.events.length+k := by
  revert hs
  induction h with
  | zero => intro hs;exact ⟨hs,by omega⟩
  | succ head tail ih =>
      intro hs
      have hh := head.event_inputs hs
      have ht := ih hh.1
      exact ⟨ht.1,by omega⟩

theorem StartedResult.event_inputs {c : Row m} {columns : Set (FractionalCover.Column m)}
    {delta : Fraction} {fuel : Bits} (r : StartedResult c columns delta fuel) :
    BinaryFractionalWidths.EventInputs c r.rest.state ∧
      r.rest.state.events.length ≤ value fuel := by
  have h := r.rest.trace.event_inputs
    (BinaryFractionalWidths.start_event_inputs c delta (cached r.first.1.choice))
  exact ⟨h.1,by simpa only [BinaryFractionalCore.start,List.length_nil,Nat.zero_add] using h.2⟩

/-- The amount width is the original supplied width, including padding. -/
theorem InputResult.events {c : Row m} {columns : Set (FractionalCover.Column m)}
    (r : InputResult c columns) (B : ℕ) (hc : BinaryFractionalWidths.RowStored c B) :
    r.rest.state.events.length ≤ 3*m^2 ∧
      ∀ e ∈ r.rest.state.events, StoredBounded e.amount B := by
  have h := r.event_inputs
  have hf := (BinaryFractionalCore.parameters_spec (BinaryFractionalCore.dimension c).1).1
  rw [(BinaryFractionalCore.dimension_spec c).1] at hf
  constructor
  · simpa only [hf,FractionalCover.fuel] using h.2
  · intro e he
    obtain ⟨i,hi⟩ := h.1 e he
    rw [hi]
    exact hc i

theorem Link.balance {c : Row m} {columns : Set (FractionalCover.Column m)}
    {p p' : Pending c columns} {s t : State m} {a : Option (Answer m)}
    (h : Link c columns p s p' t a) :
    t.events.length+p'.toList.length=s.events.length+p.toList.length+a.toList.length := by
  cases h with
  | stopped => simp
  | cached q s h => simp [cached_step_events c s q.1 h]
  | fresh a s h => simp [cached_step_events c s a.1.choice h]

theorem Link.cache_none {c : Row m} {columns : Set (FractionalCover.Column m)}
    {p p' : Pending c columns} {s t : State m} {a : Option (Answer m)}
    (h : Link c columns p s p' t a) (hp : p=none) : p'=none := by
  cases h with
  | stopped => exact hp
  | cached => cases hp
  | fresh => rfl

theorem Link.active_clears {c : Row m} {columns : Set (FractionalCover.Column m)}
    {p p' : Pending c columns} {s t : State m} {a : Option (Answer m)}
    (h : Link c columns p s p' t a) (hs : (guard c s).1=false) : p'=none := by
  cases h with
  | stopped p s h => rw [h] at hs;cases hs
  | cached => rfl
  | fresh => rfl

theorem Trace.balance {c : Row m} {columns : Set (FractionalCover.Column m)}
    {k : ℕ} {p p' : Pending c columns} {s t : State m} {answers : List (Answer m)}
    (h : Trace c columns k p s p' t answers) :
    t.events.length+p'.toList.length=s.events.length+p.toList.length+answers.length := by
  induction h with
  | zero => simp
  | succ head tail ih =>
      have hh := head.balance
      simp only [List.length_append]
      omega

theorem Trace.cache_none {c : Row m} {columns : Set (FractionalCover.Column m)}
    {k : ℕ} {p p' : Pending c columns} {s t : State m} {answers : List (Answer m)}
    (h : Trace c columns k p s p' t answers) (hp : p=none) : p'=none := by
  revert hp
  induction h with
  | zero => exact id
  | succ head tail ih => exact fun hp => ih (head.cache_none hp)

theorem Trace.active_clears {c : Row m} {columns : Set (FractionalCover.Column m)}
    {k : ℕ} {p p' : Pending c columns} {s t : State m} {answers : List (Answer m)}
    (h : Trace c columns k p s p' t answers) (hk : 0<k)
    (hs : (guard c s).1=false) : p'=none := by
  cases h with
  | zero => omega
  | succ head tail => exact tail.cache_none (head.active_clears hs)

theorem guard_spec (c : Row m) (s : State m) :
    (guard c s).1=true ↔ 1 ≤ FractionalCover.objective (capacities c) (stateValue s).weights := by
  change (BinaryRational.le one (objective c s.weights).1).1=true ↔ _
  rw [BinaryRational.le_decode,decode_one,BinaryFractionalRows.objective_decode,
    FractionalCoverRawCore.code_le_iff,FractionalCoverRawCore.rational_one,
    FractionalCoverRawCore.objectiveCode_value]
  rfl

theorem guard_active (c : Row m) (s : State m) :
    (guard c s).1=false ↔ FractionalCover.objective (capacities c) (stateValue s).weights < 1 := by
  rw [Bool.eq_false_iff]
  exact (not_congr (guard_spec c s)).trans not_le

theorem cached_step_value (c : Row m) (q : Choice m) (s : State m) :
    stateValue (BinaryFractionalCore.step c (cached q) s).1 =
      FractionalCover.step (capacities c) (fun _ => BinaryFractionalCore.decodeChoice q)
        (stateValue s) := by
  unfold stateValue
  rw [BinaryFractionalCore.step_refines c (cached q)
    (fun _ => BinaryFractionalCore.decodeChoice q) (by intro y;rfl)]
  exact FractionalCoverRawCore.step_refines _ _ _ (by intro y;rfl) _

theorem cached_start_value (c : Row m) (delta : Fraction) (q : Choice m)
    (hd : decode delta=FractionalCoverRawCore.deltaCode m) :
    stateValue (BinaryFractionalCore.start c delta (cached q)).1 =
      FractionalCover.start (capacities c) (fun _ => BinaryFractionalCore.decodeChoice q) := by
  unfold stateValue
  rw [BinaryFractionalCore.start_refines c delta (cached q)
    (fun _ => BinaryFractionalCore.decodeChoice q) (by intro y;rfl) hd]
  exact FractionalCoverRawCore.start_refines _ _ _ (by intro y;rfl)

/-- The numerical progress invariant has no alpha or quality premise. -/
structure ProgressInvariant (c : Row m) (s : State m) : Prop where
  positive : ∀ i, 0 < FractionalCover.value (stateValue s).weights i
  initial_le : ∀ i, FractionalCover.delta m ≤
    FractionalCover.value (capacities c) i*FractionalCover.value (stateValue s).weights i

theorem start_progress (c : Row m) (delta : Fraction) (q : Choice m)
    (hd : decode delta=FractionalCoverRawCore.deltaCode m) (hm : 0 < m)
    (hc : ∀ i, 0 < FractionalCover.value (capacities c) i) :
    ProgressInvariant c (BinaryFractionalCore.start c delta (cached q)).1 := by
  have hv := cached_start_value c delta q hd
  constructor
  · rw [hv]
    exact FractionalCover.initial_pos (capacities c) hm hc
  · intro i
    rw [hv]
    exact (FractionalCover.initial_scaled (capacities c) hc i).ge

theorem cached_step_progress (c : Row m) (columns : Set (FractionalCover.Column m))
    (s : State m) (q : Choice m) (hq : SafeChoice c columns q)
    (hc : ∀ i, 0 < FractionalCover.value (capacities c) i)
    (hs : ProgressInvariant c s) (ha : (guard c s).1=false) :
    ProgressInvariant c (BinaryFractionalCore.step c (cached q) s).1 ∧
    FractionalCover.objective (capacities c) (stateValue s).weights+FractionalCover.delta m/2 ≤
      FractionalCover.objective (capacities c)
        (stateValue (BinaryFractionalCore.step c (cached q) s).1).weights := by
  have hactive := (guard_active c s).mp ha
  have hstop : ¬1 ≤ FractionalCover.objective (capacities c) (stateValue s).weights :=
    not_le.mpr hactive
  have hu := FractionalCover.update_pos (capacities c) (stateValue s).weights
    (BinaryFractionalCore.decodeChoice q) hc hs.positive
  have hi := FractionalCover.objective_increment (capacities c) (stateValue s).weights
    (BinaryFractionalCore.decodeChoice q) hc hs.positive hq.2.1 hs.initial_le
  constructor
  · constructor
    · rw [cached_step_value]
      simpa only [FractionalCover.step,ite_eq_right hstop] using hu
    · intro i
      rw [cached_step_value]
      simp only [FractionalCover.step,ite_eq_right hstop]
      exact (hs.initial_le i).trans (mul_le_mul_of_nonneg_left
        (FractionalCover.update_mono (capacities c) (stateValue s).weights
          (BinaryFractionalCore.decodeChoice q) hc (fun j => (hs.positive j).le) i)
        (hc i).le)
  · rw [cached_step_value]
    simpa only [FractionalCover.step,ite_eq_right hstop] using hi

theorem Link.progress {c : Row m} {columns : Set (FractionalCover.Column m)}
    {p p' : Pending c columns} {s t : State m} {a : Option (Answer m)}
    (h : Link c columns p s p' t a) (hm : 0 < m)
    (hc : ∀ i, 0 < FractionalCover.value (capacities c) i) (hs : ProgressInvariant c s) :
    ProgressInvariant c t ∧
    FractionalCover.objective (capacities c) (stateValue s).weights ≤
      FractionalCover.objective (capacities c) (stateValue t).weights ∧
    (FractionalCover.objective (capacities c) (stateValue s).weights < 1 →
      FractionalCover.objective (capacities c) (stateValue s).weights+FractionalCover.delta m/2 ≤
        FractionalCover.objective (capacities c) (stateValue t).weights) := by
  have hd := FractionalCover.delta_pos hm
  cases h with
  | stopped p s h =>
      exact ⟨hs,le_rfl,fun ha => False.elim (not_lt_of_ge ((guard_spec c s).mp h) ha)⟩
  | cached q s h =>
      have ht := cached_step_progress c columns s q.1 q.2 hc hs h
      exact ⟨ht.1,by linarith [ht.2],fun _ => ht.2⟩
  | fresh a s h =>
      have ht := cached_step_progress c columns s a.1.choice a.2 hc hs h
      exact ⟨ht.1,by linarith [ht.2],fun _ => ht.2⟩

theorem Trace.progress {c : Row m} {columns : Set (FractionalCover.Column m)}
    {k : ℕ} {p p' : Pending c columns} {s t : State m} {answers : List (Answer m)}
    (h : Trace c columns k p s p' t answers) (hm : 0 < m)
    (hc : ∀ i, 0 < FractionalCover.value (capacities c) i) (hs : ProgressInvariant c s) :
    ProgressInvariant c t ∧
    (1 ≤ FractionalCover.objective (capacities c) (stateValue t).weights ∨
      FractionalCover.objective (capacities c) (stateValue s).weights+
        k*(FractionalCover.delta m/2) ≤
          FractionalCover.objective (capacities c) (stateValue t).weights) := by
  revert hs
  induction h with
  | zero => intro hs;exact ⟨hs,Or.inr (by simp)⟩
  | @succ k p p' p'' s t u answer answers head tail ih =>
      intro hs
      have hh := head.progress hm hc hs
      have ht := ih hh.1
      refine ⟨ht.1,?_⟩
      rcases ht.2 with hstop | hgrow
      · exact Or.inl hstop
      · by_cases hstop : 1 ≤ FractionalCover.objective (capacities c) (stateValue u).weights
        · exact Or.inl hstop
        · have hd := FractionalCover.delta_pos hm
          have hkn : 0 ≤ (k : ℚ)*(FractionalCover.delta m/2) := by positivity
          have ha : FractionalCover.objective (capacities c) (stateValue s).weights < 1 := by
            linarith [hh.2.1]
          have hi := hh.2.2 ha
          right
          push_cast
          nlinarith

/-- Every structurally valid trace stops by the same fixed horizon, even if
some chosen cuts violate every proposed approximation budget. -/
theorem Trace.stopped {c : Row m} {columns : Set (FractionalCover.Column m)}
    {p p' : Pending c columns} {s t : State m} {answers : List (Answer m)}
    (h : Trace c columns (FractionalCover.fuel m) p s p' t answers) (hm : 0 < m)
    (hc : ∀ i, 0 < FractionalCover.value (capacities c) i) (hs : ProgressInvariant c s) :
    1 ≤ FractionalCover.objective (capacities c) (stateValue t).weights := by
  rcases (h.progress hm hc hs).2 with hstop | hgrow
  · exact hstop
  · have hf : (FractionalCover.fuel m : ℚ)*(FractionalCover.delta m/2)=1 := by
      unfold FractionalCover.fuel FractionalCover.delta
      push_cast
      field_simp [ne_of_gt (show (0 : ℚ)< m by exact_mod_cast hm)]
    rw [hf] at hgrow
    have hp := FractionalCover.objective_pos (capacities c) (stateValue s).weights hm hc hs.positive
    linarith

theorem InputResult.stopped {c : Row m} {columns : Set (FractionalCover.Column m)}
    (r : InputResult c columns) (hm : 0 < m)
    (hc : ∀ i, 0 < FractionalCover.value (capacities c) i) :
    1 ≤ FractionalCover.objective (capacities c) (stateValue r.rest.state).weights := by
  have hp := BinaryFractionalCore.parameters_spec (BinaryFractionalCore.dimension c).1
  rw [(BinaryFractionalCore.dimension_spec c).1] at hp
  have hs := start_progress c _ r.first.1.choice hp.2 hm hc
  have ht := Eq.mp (congrArg (fun k => Trace c columns k
    (some ⟨r.first.1.choice,r.first.2⟩)
    (BinaryFractionalCore.start c
      (BinaryFractionalCore.parameters (BinaryFractionalCore.dimension c).1).delta
      (cached r.first.1.choice)).1 r.rest.pending r.rest.state r.rest.answers) hp.1) r.rest.trace
  exact ht.stopped hm hc hs

theorem initial_active (c : Row m) (delta : Fraction) (q : Choice m)
    (hd : decode delta=FractionalCoverRawCore.deltaCode m) (hm : 0 < m)
    (hc : ∀ i, 0 < FractionalCover.value (capacities c) i) :
    (guard c (BinaryFractionalCore.start c delta (cached q)).1).1=false := by
  apply (guard_active c _).mpr
  rw [cached_start_value c delta q hd]
  change FractionalCover.objective (capacities c) (FractionalCover.initial (capacities c)) < 1
  rw [FractionalCover.objective_initial (capacities c) hc]
  have hmQ : (0 : ℚ)< m := by exact_mod_cast hm
  have hmOne : (1 : ℚ)≤ m := by exact_mod_cast hm
  calc
    (m : ℚ)*FractionalCover.delta m = 2/(3*(m : ℚ)) := by
      unfold FractionalCover.delta
      field_simp [ne_of_gt hmQ]
    _ ≤ 2/3 := by
      apply (div_le_div_iff₀ (by positivity) (by norm_num : (0 : ℚ)<3)).mpr
      nlinarith
    _ < 1 := by norm_num

theorem InputResult.cache_empty {c : Row m} {columns : Set (FractionalCover.Column m)}
    (r : InputResult c columns) (hm : 0 < m)
    (hc : ∀ i, 0 < FractionalCover.value (capacities c) i) : r.rest.pending=none := by
  have hp := BinaryFractionalCore.parameters_spec (BinaryFractionalCore.dimension c).1
  rw [(BinaryFractionalCore.dimension_spec c).1] at hp
  apply r.rest.trace.active_clears
  · rw [hp.1]
    unfold FractionalCover.fuel
    positivity
  · exact initial_active c _ r.first.1.choice hp.2 hm hc

theorem StartedResult.call_balance {c : Row m} {columns : Set (FractionalCover.Column m)}
    {delta : Fraction} {fuel : Bits} (r : StartedResult c columns delta fuel) :
    r.rest.state.events.length+r.rest.pending.toList.length=r.answers.length := by
  have h := r.rest.trace.balance
  simpa [StartedResult.answers,BinaryFractionalCore.start,Nat.add_comm] using h

/-- One actual provider call per retained event, including the shared first one. -/
theorem InputResult.calls_eq_events {c : Row m} {columns : Set (FractionalCover.Column m)}
    (r : InputResult c columns) (hm : 0 < m)
    (hc : ∀ i, 0 < FractionalCover.value (capacities c) i) :
    r.answers.length=r.rest.state.events.length := by
  have h := r.call_balance
  rw [r.cache_empty hm hc] at h
  simpa using h.symm

def EventSafe (c : Row m) (columns : Set (FractionalCover.Column m)) (e : Event m) : Prop :=
  SafeChoice c columns e.choice ∧ e.amount=get c e.choice.bottleneck

theorem Link.events_safe {c : Row m} {columns : Set (FractionalCover.Column m)}
    {p p' : Pending c columns} {s t : State m} {a : Option (Answer m)}
    (h : Link c columns p s p' t a) (hs : ∀ e ∈ s.events, EventSafe c columns e) :
    ∀ e ∈ t.events, EventSafe c columns e := by
  cases h with
  | stopped => exact hs
  | cached q s h =>
      rw [cached_step_events c s q.1 h]
      intro e he
      rcases List.mem_cons.mp he with rfl | he
      · exact ⟨q.2,rfl⟩
      · exact hs e he
  | fresh a s h =>
      rw [cached_step_events c s a.1.choice h]
      intro e he
      rcases List.mem_cons.mp he with rfl | he
      · exact ⟨a.2,rfl⟩
      · exact hs e he

theorem Trace.events_safe {c : Row m} {columns : Set (FractionalCover.Column m)}
    {k : ℕ} {p p' : Pending c columns} {s t : State m} {answers : List (Answer m)}
    (h : Trace c columns k p s p' t answers) (hs : ∀ e ∈ s.events, EventSafe c columns e) :
    ∀ e ∈ t.events, EventSafe c columns e := by
  revert hs
  induction h with
  | zero => exact id
  | succ head tail ih => exact fun hs => ih (head.events_safe hs)

theorem StartedResult.events_safe {c : Row m} {columns : Set (FractionalCover.Column m)}
    {delta : Fraction} {fuel : Bits} (r : StartedResult c columns delta fuel) :
    ∀ e ∈ r.rest.state.events, EventSafe c columns e := by
  apply r.rest.trace.events_safe
  simp [BinaryFractionalCore.start]

def eventTotal (es : List (Event m)) : ℚ :=
  (es.map (fun e => FractionalCoverRawCore.rational (decode e.amount))).sum

theorem capacities_value (c : Row m) (i : Fin m) :
    FractionalCover.value (capacities c) i=
      FractionalCoverRawCore.rational (decode (get c i)) := by
  simp [capacities,FractionalCoverRawCore.decode_value,BinaryFractionalRows.decode_get]

theorem cached_step_total (c : Row m) (s : State m) (q : Choice m)
    (h : (guard c s).1=false) :
    (stateValue (BinaryFractionalCore.step c (cached q) s).1).total=
      (stateValue s).total+FractionalCoverRawCore.rational (decode (get c q.bottleneck)) := by
  have ha := (guard_active c s).mp h
  rw [cached_step_value]
  simp only [FractionalCover.step,ite_eq_right (not_le.mpr ha),capacities_value]
  rfl

theorem Link.total_eq {c : Row m} {columns : Set (FractionalCover.Column m)}
    {p p' : Pending c columns} {s t : State m} {a : Option (Answer m)}
    (h : Link c columns p s p' t a) (hs : (stateValue s).total=eventTotal s.events) :
    (stateValue t).total=eventTotal t.events := by
  cases h with
  | stopped => exact hs
  | cached q s h =>
      rw [cached_step_total c s q.1 h,cached_step_events c s q.1 h,hs]
      simp [eventTotal,add_comm]
  | fresh a s h =>
      rw [cached_step_total c s a.1.choice h,cached_step_events c s a.1.choice h,hs]
      simp [eventTotal,add_comm]

theorem Trace.total_eq {c : Row m} {columns : Set (FractionalCover.Column m)}
    {k : ℕ} {p p' : Pending c columns} {s t : State m} {answers : List (Answer m)}
    (h : Trace c columns k p s p' t answers) (hs : (stateValue s).total=eventTotal s.events) :
    (stateValue t).total=eventTotal t.events := by
  revert hs
  induction h with
  | zero => exact id
  | succ head tail ih => exact fun hs => ih (head.total_eq hs)

theorem StartedResult.total_eq {c : Row m} {columns : Set (FractionalCover.Column m)}
    {delta : Fraction} {fuel : Bits} (r : StartedResult c columns delta fuel) :
    (stateValue r.rest.state).total=eventTotal r.rest.state.events := by
  apply r.rest.trace.total_eq
  simp [stateValue,BinaryFractionalCore.start,BinaryFractionalCore.decodeState,
    FractionalCoverRawCore.decodeState,eventTotal]

theorem eventTotal_nonneg (es : List (Event m))
    (h : ∀ e ∈ es, 0 ≤ FractionalCoverRawCore.rational (decode e.amount)) : 0 ≤ eventTotal es := by
  induction es with
  | nil => simp [eventTotal]
  | cons e es ih =>
      have he := h e List.mem_cons_self
      have ht := ih (fun a ha => h a (List.mem_cons_of_mem e ha))
      simpa only [eventTotal,List.map_cons,List.sum_cons] using add_nonneg he ht

theorem eventTotal_pos (es : List (Event m)) (hne : es≠[])
    (h : ∀ e ∈ es, 0 < FractionalCoverRawCore.rational (decode e.amount)) : 0 < eventTotal es := by
  cases es with
  | nil => exact False.elim (hne rfl)
  | cons e es =>
      have he := h e List.mem_cons_self
      have ht := eventTotal_nonneg es (fun a ha => (h a (List.mem_cons_of_mem e ha)).le)
      simpa only [eventTotal,List.map_cons,List.sum_cons] using add_pos_of_pos_of_nonneg he ht

/-- Positive total and structurally valid events hold on cost-bad traces too. -/
theorem InputResult.total_positive {c : Row m} {columns : Set (FractionalCover.Column m)}
    (r : InputResult c columns) (hm : 0 < m)
    (hc : ∀ i, 0 < FractionalCover.value (capacities c) i) :
    0 < eventTotal r.rest.state.events ∧ 0 < (stateValue r.rest.state).total := by
  have hlen : 0 < r.rest.state.events.length := by
    rw [← r.calls_eq_events hm hc]
    simp [StartedResult.answers]
  have hne : r.rest.state.events≠[] := by intro h;rw [h] at hlen;cases hlen
  have hpos := eventTotal_pos r.rest.state.events hne (by
    intro e he
    have hs := r.events_safe e he
    rw [hs.2,← capacities_value]
    exact hc e.choice.bottleneck)
  exact ⟨hpos,by rw [r.total_eq];exact hpos⟩

/-- Count every physical guard, including the deliberately repeated active one. -/
theorem InputResult.guard_count {c : Row m} {columns : Set (FractionalCover.Column m)}
    (r : InputResult c columns) :
    r.rest.stopTests=3*m^2 ∧
      r.rest.guardTests=3*m^2+r.rest.state.events.length := by
  have hp := (BinaryFractionalCore.parameters_spec (BinaryFractionalCore.dimension c).1).1
  rw [(BinaryFractionalCore.dimension_spec c).1] at hp
  constructor
  · simpa only [hp,FractionalCover.fuel] using r.rest.stopTests_eq
  · have h := r.rest.guardTests_balance
    simpa only [BinaryFractionalCore.start,List.length_nil,Nat.add_zero,hp,
      FractionalCover.fuel] using h

end DirectedFlowCutGap.BinaryApproximatePacking
