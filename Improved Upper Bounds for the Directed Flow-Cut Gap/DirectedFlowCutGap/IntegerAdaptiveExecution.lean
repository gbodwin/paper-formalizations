import DirectedFlowCutGap.RetainedGridState

/-!
# Bounded adaptive control over retained integer arrays

The supplied random input is finite: a list of original demand labels and one
cell index per label for each epoch. Every branch uses natural numbers or
Booleans. Each refresh materializes its candidate family once and retains it;
successful ready tests never recompute it. Every sampled round invalidates the
old candidates and performs one explicit refresh for the new state.

The counters below count actual calls and control events of these recurrences.
They are not a machine-instruction or bit-cost theorem. Implementations of the
two certified adapters, uniform input generation, and their costs must still
be composed before making a complete runtime claim.
-/
namespace DirectedFlowCutGap.IntegerAdaptiveExecution
open scoped BigOperators NNReal
open CandidateSchedule CandidateSchedule.State FlexibleCandidateSchedule
open RetainedGridState

/-- Each counter names an actual event in the recurrence, not an oracle budget. -/
structure Work where
  families : ℕ := 0
  candidates : ℕ := 0
  gates : ℕ := 0
  epochTests : ℕ := 0
  rounds : ℕ := 0
  restarts : ℕ := 0
  massScans : ℕ := 0
deriving Repr, DecidableEq

def Work.add (a b : Work) : Work :=
  ⟨a.families + b.families, a.candidates + b.candidates,
    a.gates + b.gates, a.epochTests + b.epochTests,
    a.rounds + b.rounds, a.restarts + b.restarts, a.massScans + b.massScans⟩

def Work.control (a : Work) : ℕ :=
  a.gates + a.epochTests + a.rounds + a.restarts + a.massScans

section
variable {n L : ℕ} {G : Digraph (Fin n)} {D : Finset (Pair n)}
variable {selector : FamilyProvider G D (L : ℝ≥0) → Prop}
variable {H : ∃ P, selector P}
local notation "P" => selectedProvider H

def refreshWork (s : Code G D L) : Work :=
  { families := 1, candidates := (remainingSet s.data.remaining).card, massScans := 1 }

structure Result (H : ∃ Q, selector Q) where
  cache : Cache H
  work : Work

/-- Starting a run performs and counts the initial optimization. -/
def start (Q : Optimizer H) (s : Code G D L) : Result H :=
  ⟨refresh Q s, refreshWork s⟩

/-- Exactly one cached integer gate, followed by at most one installation and
one new family computation. No coordinate access invokes a solver. -/
def advance (Q : Optimizer H) (R : ℕ) (c : Cache H) : Result H :=
  if c.ready R then ⟨c, { gates := 1 }⟩ else
    let s := c.install
    ⟨refresh Q s, ({ gates := 1, restarts := 1 } : Work).add (refreshWork s)⟩

theorem advance_refines (Q : Optimizer H) (hL : 0 < L) (R : ℕ) (c : Cache H) :
    interpret (advance Q R c).cache.state =
      (interpret c.state).selectedAdvance P (R : ℝ≥0) := by
  unfold advance State.selectedAdvance
  split_ifs with h₁ h₂ h₂
  · rfl
  · exact (h₂ ((c.ready_correct hL R).mp h₁)).elim
  · exact (h₁ ((c.ready_correct hL R).mpr h₂)).elim
  · exact c.interpret_install

/-- Fixed finite fuel is part of the executable input. Once ready, only cheap
cached gates remain; no further optimizer is called. -/
def stabilize (Q : Optimizer H) (R : ℕ) : ℕ → Cache H → Result H
  | 0, c => ⟨c, {}⟩
  | fuel + 1, c =>
      let a := advance Q R c
      let b := stabilize Q R fuel a.cache
      ⟨b.cache, a.work.add b.work⟩

theorem trajectory_shift (R fuel : ℕ) (s : State G D (L : ℝ≥0)) :
    (s.selectedAdvance P (R : ℝ≥0)).selectedTrajectory P (R : ℝ≥0) fuel =
      s.selectedTrajectory P (R : ℝ≥0) (fuel + 1) := by
  induction fuel with
  | zero => rfl
  | succ fuel ih => simp only [selectedTrajectory_succ, ih]

theorem stabilize_refines (Q : Optimizer H) (hL : 0 < L) (R fuel : ℕ)
    (c : Cache H) :
    interpret (stabilize Q R fuel c).cache.state =
      (interpret c.state).selectedTrajectory P (R : ℝ≥0) fuel := by
  induction fuel generalizing c with
  | zero => rfl
  | succ fuel ih =>
      simp only [stabilize]
      rw [ih, advance_refines Q hL]
      exact trajectory_shift R fuel _

/-- Sufficient geometric fuel identifies the actual retained result with the
flexible law's first-ready state, including the selected weight vector. -/
theorem stabilize_eq_selectedStabilize (Q : Optimizer H) (hL : 0 < L)
    (R fuel : ℕ) (hR : 1 < (R : ℝ≥0)) (c : Cache H)
    (hfuel : (interpret c.state).mass < (R : ℝ≥0) ^ fuel) :
    interpret (stabilize Q R fuel c).cache.state =
      (interpret c.state).selectedStabilize P (R : ℝ≥0) hR := by
  rw [stabilize_refines Q hL]
  exact selectedTrajectory_eq_stabilize P _ hR _ fuel hfuel

theorem advance_trace (Q : Optimizer H) (hL : 0 < L) (R : ℕ) (c : Cache H) :
    Trace P (R : ℝ≥0) (interpret c.state) (advance Q R c).work.restarts 0
      (interpret (advance Q R c).cache.state) := by
  unfold advance
  split_ifs with h
  · exact Trace.start
  · simp only [Work.add, refreshWork]
    rw [show interpret (refresh Q c.install).state =
      (interpret c.state).selectedInstall P from c.interpret_install]
    exact Trace.restart Trace.start (fun hr => h ((c.ready_correct hL R).mpr hr))

theorem stabilize_trace (Q : Optimizer H) (hL : 0 < L) (R fuel : ℕ) (c : Cache H) :
    Trace P (R : ℝ≥0) (interpret c.state) (stabilize Q R fuel c).work.restarts 0
      (interpret (stabilize Q R fuel c).cache.state) := by
  induction fuel generalizing c with
  | zero => exact Trace.start
  | succ fuel ih =>
      exact trace_trans P _ (advance_trace Q hL R c) (ih (advance Q R c).cache)

theorem stabilize_gates (Q : Optimizer H) (R fuel : ℕ) (c : Cache H) :
    (stabilize Q R fuel c).work.gates = fuel := by
  induction fuel generalizing c with
  | zero => rfl
  | succ fuel ih =>
      simp only [stabilize, Work.add, ih]
      unfold advance
      split_ifs <;> simp [Work.add, refreshWork, Nat.add_comm]

theorem stabilize_families (Q : Optimizer H) (R fuel : ℕ) (c : Cache H) :
    (stabilize Q R fuel c).work.families = (stabilize Q R fuel c).work.restarts := by
  induction fuel generalizing c with
  | zero => rfl
  | succ fuel ih =>
      simp only [stabilize, Work.add, ih]
      unfold advance
      split_ifs <;> rfl

theorem stabilize_restarts_le (Q : Optimizer H) (R fuel : ℕ) (c : Cache H) :
    (stabilize Q R fuel c).work.restarts ≤ fuel := by
  induction fuel generalizing c with
  | zero => exact le_rfl
  | succ fuel ih =>
      have hh := ih (advance Q R c).cache
      change (advance Q R c).work.restarts +
        (stabilize Q R fuel (advance Q R c).cache).work.restarts ≤ fuel + 1
      have ha : (advance Q R c).work.restarts ≤ 1 := by
        unfold advance
        split_ifs <;> simp [Work.add, refreshWork]
      omega

/-- Geometric accounting bounds the actual number of installations; the
separate family counter includes every refresh after a sampled cut as well. -/
theorem stabilize_geometric_restarts (Q : Optimizer H) (hL : 0 < L)
    (R fuel J : ℕ) (hR : 1 < (R : ℝ≥0)) (c : Cache H)
    (hJ : (interpret c.state).mass < (R : ℝ≥0) ^ (J + 1)) :
    (stabilize Q R fuel c).work.restarts ≤ J :=
  (stabilize_trace Q hL R fuel c).installations_le hR hJ

/-- Epoch-boundary decisions are also exact integer comparisons. -/
def active (R M : ℕ) (c : Cache H) : Bool :=
  c.ready R && !(c.optimal == 0) && (M ≤ R * c.state.data.current)

theorem active_correct (hL : 0 < L) (R M : ℕ) (c : Cache H) :
    active R M c = true ↔
      AdaptiveEpoch.Active (R : ℝ≥0) ((M : ℝ≥0) / L) (interpret c.state) := by
  have hLp : (0 : ℝ≥0) < L := by exact_mod_cast hL
  have hm : (M : ℝ≥0) / L ≤ (R : ℝ≥0) * (interpret c.state).mass ↔
      M ≤ R * c.state.data.current := by
    rw [interpret_mass, ← mul_div_assoc, div_le_div_iff_of_pos_right hLp]
    exact_mod_cast Iff.rfl
  simp only [active, Bool.and_eq_true, Bool.not_eq_true',
    beq_eq_false_iff_ne, decide_eq_true_eq, AdaptiveEpoch.Active,
    c.ready_correct hL R, hm]
  have hz := c.zero_correct hL
  tauto

/-- Original labels and all cell indices are finite input data. A separate
permutation certificate is needed when relating an entire epoch to its PMF. -/
structure Input (n L : ℕ) where
  order : List (Pair n)
  cells : Vector (Vector (Fin L) n) n

def Input.cell (i : Input n L) (p : Pair n) : Fin L := i.cells[p.1.val][p.2.val]

noncomputable def levels (hL : 0 < L) (i : Input n L) (p : Pair n) : AdaptiveEpoch.UnitLevel :=
  midpointLevel hL (i.cell p)

/-- Every actual cut is followed by one candidate refresh for the new state. -/
def scan (Q : Optimizer H) (hL : 0 < L) (C : CutOracle G L hL)
    (R M : ℕ) (cells : Pair n → Fin L) : List (Pair n) → Cache H → Result H
  | [], c => ⟨c, {}⟩
  | p :: ps, c =>
      if h : active R M c = true ∧ flag c.state.data.remaining p = true then
        let s := sampleRound hL C c.state p (membership_of_flag c.state p h.2) (cells p)
        let d := refresh Q s
        let b := scan Q hL C R M cells ps d
        ⟨b.cache, (({ epochTests := 1, rounds := 1, massScans := 1 } : Work).add
          (refreshWork s)).add b.work⟩
      else ⟨c, { epochTests := 1 }⟩

theorem scan_refines (Q : Optimizer H) (hL : 0 < L) (C : CutOracle G L hL)
    (R M : ℕ) (cells : Pair n → Fin L) (order : List (Pair n)) (c : Cache H) :
    interpret (scan Q hL C R M cells order c).cache.state =
      (AdaptiveEpoch.run (R : ℝ≥0) ((M : ℝ≥0) / L)
        (fun p => midpointLevel hL (cells p)) (interpret c.state) order).state := by
  induction order generalizing c with
  | nil => rfl
  | cons p ps ih =>
      have he : (active R M c = true ∧ flag c.state.data.remaining p = true) ↔
          (AdaptiveEpoch.Active (R : ℝ≥0) ((M : ℝ≥0) / L) (interpret c.state) ∧
            p ∈ (interpret c.state).remaining) := by
        rw [active_correct hL, ← mem_remainingSet]
        rfl
      simp only [scan, AdaptiveEpoch.run]
      split_ifs with h₁ h₂ h₂
      · rw [ih]
        simp only [refresh, interpret_sampleRound]
      · exact (h₂ (he.mp h₁)).elim
      · exact (h₁ (he.mpr h₂)).elim
      · rfl

theorem scan_rounds_refine (Q : Optimizer H) (hL : 0 < L) (C : CutOracle G L hL)
    (R M : ℕ) (cells : Pair n → Fin L) (order : List (Pair n)) (c : Cache H) :
    (scan Q hL C R M cells order c).work.rounds =
      (AdaptiveEpoch.run (R : ℝ≥0) ((M : ℝ≥0) / L)
        (fun p => midpointLevel hL (cells p)) (interpret c.state) order).rounds := by
  induction order generalizing c with
  | nil => rfl
  | cons p ps ih =>
      have he : (active R M c = true ∧ flag c.state.data.remaining p = true) ↔
          (AdaptiveEpoch.Active (R : ℝ≥0) ((M : ℝ≥0) / L) (interpret c.state) ∧
            p ∈ (interpret c.state).remaining) := by
        rw [active_correct hL, ← mem_remainingSet]
        rfl
      simp only [scan, AdaptiveEpoch.run]
      split_ifs with h₁ h₂ h₂
      · simp only [Work.add, refreshWork, Nat.zero_add, Nat.add_zero, ih]
        simp only [refresh, interpret_sampleRound]
        omega
      · exact (h₂ (he.mp h₁)).elim
      · exact (h₁ (he.mpr h₂)).elim
      · rfl

theorem scan_families (Q : Optimizer H) (hL : 0 < L) (C : CutOracle G L hL)
    (R M : ℕ) (cells : Pair n → Fin L) (order : List (Pair n)) (c : Cache H) :
    (scan Q hL C R M cells order c).work.families =
      (scan Q hL C R M cells order c).work.rounds := by
  induction order generalizing c with
  | nil => rfl
  | cons p ps ih =>
      simp only [scan]
      split_ifs
      · simp only [Work.add, refreshWork, Nat.zero_add, Nat.add_zero, ih]
      · rfl

/-- The deterministic outer recursion consumes a finite list of supplied
epoch samples. Its base case still performs bounded stabilization. -/
def execute (Q : Optimizer H) (hL : 0 < L) (C : CutOracle G L hL)
    (R fuel : ℕ) : List (Input n L) → Cache H → Result H
  | [], c => stabilize Q R fuel c
  | i :: inputs, c =>
      let a := stabilize Q R fuel c
      if a.cache.optimal == 0 then a else
        let b := scan Q hL C R a.cache.state.data.current i.cell i.order a.cache
        let d := execute Q hL C R fuel inputs b.cache
        ⟨d.cache, a.work.add (b.work.add d.work)⟩

/-- Public entry from integer state data: the initial refresh is executed and
included in the returned counters, even if the instance is already terminal. -/
def run (Q : Optimizer H) (hL : 0 < L) (C : CutOracle G L hL)
    (R fuel : ℕ) (inputs : List (Input n L)) (s : Code G D L) : Result H :=
  let a := start Q s
  let b := execute Q hL C R fuel inputs a.cache
  ⟨b.cache, a.work.add b.work⟩

attribute [local instance] Classical.propDecidable

/-- A state-level specification using precisely the flexible provider's
transition and the actual endpoint-safe epoch scan. -/
noncomputable def reference (hL : 0 < L) (R fuel : ℕ) :
    List (Input n L) → State G D (L : ℝ≥0) → State G D (L : ℝ≥0)
  | [], s => s.selectedTrajectory P (R : ℝ≥0) fuel
  | i :: inputs, s =>
      let t := s.selectedTrajectory P (R : ℝ≥0) fuel
      if t.optimum = 0 then t else
        reference hL R fuel inputs
          (AdaptiveEpoch.run (R : ℝ≥0) t.mass (levels hL i) t i.order).state

/-- State equality includes remaining labels, cut, every retained weight, and
scale. It does not identify the selected vector with the compact selector. -/
theorem execute_refines (Q : Optimizer H) (hL : 0 < L) (C : CutOracle G L hL)
    (R fuel : ℕ) (inputs : List (Input n L)) (c : Cache H) :
    interpret (execute Q hL C R fuel inputs c).cache.state =
      reference (H := H) hL R fuel inputs (interpret c.state) := by
  induction inputs generalizing c with
  | nil => exact stabilize_refines Q hL R fuel c
  | cons i inputs ih =>
      simp only [execute, reference]
      rw [← stabilize_refines Q hL R fuel c]
      split_ifs with h₁ h₂ h₂
      · rfl
      · exact (h₂ (((stabilize Q R fuel c).cache.zero_correct hL).mp
          (by simpa only [beq_iff_eq] using h₁))).elim
      · exact (h₁ (by simpa only [beq_iff_eq] using
          ((stabilize Q R fuel c).cache.zero_correct hL).mpr h₂)).elim
      · rw [ih, scan_refines Q hL, interpret_mass]
        rfl

theorem execute_cut_refines (Q : Optimizer H) (hL : 0 < L) (C : CutOracle G L hL)
    (R fuel : ℕ) (inputs : List (Input n L)) (c : Cache H) :
    cutSet (execute Q hL C R fuel inputs c).cache.state.data.cut =
      (reference (H := H) hL R fuel inputs (interpret c.state)).cut :=
  congrArg State.cut (execute_refines Q hL C R fuel inputs c)

theorem stabilize_rounds (Q : Optimizer H) (R fuel : ℕ) (c : Cache H) :
    (stabilize Q R fuel c).work.rounds = 0 := by
  induction fuel generalizing c with
  | zero => rfl
  | succ fuel ih =>
      simp only [stabilize, Work.add, ih, Nat.add_zero]
      unfold advance
      split_ifs <;> rfl

theorem scan_restarts (Q : Optimizer H) (hL : 0 < L) (C : CutOracle G L hL)
    (R M : ℕ) (cells : Pair n → Fin L) (order : List (Pair n)) (c : Cache H) :
    (scan Q hL C R M cells order c).work.restarts = 0 := by
  induction order generalizing c with
  | nil => rfl
  | cons p ps ih =>
      simp only [scan]
      split_ifs
      · simp only [Work.add, refreshWork, Nat.zero_add, ih]
      · rfl

theorem scan_trace (Q : Optimizer H) (hL : 0 < L) (C : CutOracle G L hL)
    (R M : ℕ) (cells : Pair n → Fin L) (order : List (Pair n)) (c : Cache H) :
    Trace P (R : ℝ≥0) (interpret c.state) (scan Q hL C R M cells order c).work.restarts
      (scan Q hL C R M cells order c).work.rounds
      (interpret (scan Q hL C R M cells order c).cache.state) := by
  rw [scan_restarts, scan_rounds_refine Q hL, scan_refines Q hL]
  simpa only [Nat.zero_add] using FlexibleCandidateSchedule.run_trace (R : ℝ≥0) ((M : ℝ≥0) / L)
    (fun p => midpointLevel hL (cells p)) order
    (show Trace P (R : ℝ≥0) (interpret c.state) 0 0 (interpret c.state) from Trace.start)

theorem execute_trace (Q : Optimizer H) (hL : 0 < L) (C : CutOracle G L hL)
    (R fuel : ℕ) (inputs : List (Input n L)) (c : Cache H) :
    Trace P (R : ℝ≥0) (interpret c.state) (execute Q hL C R fuel inputs c).work.restarts
      (execute Q hL C R fuel inputs c).work.rounds
      (interpret (execute Q hL C R fuel inputs c).cache.state) := by
  induction inputs generalizing c with
  | nil =>
      rw [execute, stabilize_rounds]
      exact stabilize_trace Q hL R fuel c
  | cons i inputs ih =>
      simp only [execute]
      split_ifs
      · rw [stabilize_rounds]
        exact stabilize_trace Q hL R fuel c
      · have hs := stabilize_trace Q hL R fuel c
        have he := scan_trace Q hL C R (stabilize Q R fuel c).cache.state.data.current
          i.cell i.order (stabilize Q R fuel c).cache
        have ht := trace_trans P _ hs (trace_trans P _ he (ih _))
        simpa only [Work.add, stabilize_rounds, Nat.zero_add] using ht

/-- Actual family solves include failed restart tests and post-cut refreshes.
The initial `start` contributes one additional family computation. -/
theorem execute_families (Q : Optimizer H) (hL : 0 < L) (C : CutOracle G L hL)
    (R fuel : ℕ) (inputs : List (Input n L)) (c : Cache H) :
    (execute Q hL C R fuel inputs c).work.families =
      (execute Q hL C R fuel inputs c).work.restarts +
      (execute Q hL C R fuel inputs c).work.rounds := by
  induction inputs generalizing c with
  | nil => simp only [execute, stabilize_families, stabilize_rounds, Nat.add_zero]
  | cons i inputs ih =>
      simp only [execute]
      split_ifs
      · simp only [stabilize_families, stabilize_rounds, Nat.add_zero]
      · simp only [Work.add, stabilize_families, scan_families, stabilize_rounds,
          scan_restarts, ih, Nat.zero_add]
        omega

theorem execute_rounds_le (Q : Optimizer H) (hL : 0 < L) (C : CutOracle G L hL)
    (R fuel : ℕ) (inputs : List (Input n L)) (c : Cache H) :
    (execute Q hL C R fuel inputs c).work.rounds ≤
      (remainingSet c.state.data.remaining).card := by
  have h := (execute_trace Q hL C R fuel inputs c).rounds_card
  change _ + _ = (remainingSet c.state.data.remaining).card at h
  omega

theorem execute_restarts_le (Q : Optimizer H) (hL : 0 < L) (C : CutOracle G L hL)
    (R fuel J : ℕ) (hR : 1 < (R : ℝ≥0)) (inputs : List (Input n L)) (c : Cache H)
    (hJ : (interpret c.state).mass < (R : ℝ≥0) ^ (J + 1)) :
    (execute Q hL C R fuel inputs c).work.restarts ≤ J :=
  (execute_trace Q hL C R fuel inputs c).installations_le hR hJ

/-- Even without a legal-permutation input certificate, every reported zero
is a valid cut for all original demands. -/
theorem execute_zero_valid (Q : Optimizer H) (hL : 0 < L) (C : CutOracle G L hL)
    (R fuel : ℕ) (inputs : List (Input n L)) (c : Cache H)
    (hz : (execute Q hL C R fuel inputs c).cache.optimal = 0) :
    IsIntegralCut G (cutSet (execute Q hL C R fuel inputs c).cache.state.data.cut)
      (D : Set (Pair n)) :=
  (interpret (execute Q hL C R fuel inputs c).cache.state).integralCut_of_zero
    (((execute Q hL C R fuel inputs c).cache.zero_correct hL).mp hz)

theorem refresh_candidates_le (s : Code G D L) :
    (refreshWork s).candidates ≤ n * n := by
  simpa [refreshWork, Fintype.card_prod] using (remainingSet s.data.remaining).card_le_univ

theorem advance_candidates_le (Q : Optimizer H) (R : ℕ) (c : Cache H) :
    (advance Q R c).work.candidates ≤ n * n * (advance Q R c).work.families := by
  unfold advance
  split_ifs
  · simp
  · simpa [Work.add, refreshWork] using refresh_candidates_le c.install

theorem stabilize_candidates_le (Q : Optimizer H) (R fuel : ℕ) (c : Cache H) :
    (stabilize Q R fuel c).work.candidates ≤ n * n *
      (stabilize Q R fuel c).work.families := by
  induction fuel generalizing c with
  | zero => simp [stabilize]
  | succ fuel ih =>
      have ha := advance_candidates_le Q R c
      have hb := ih (advance Q R c).cache
      change (advance Q R c).work.candidates +
        (stabilize Q R fuel (advance Q R c).cache).work.candidates ≤
        n * n * ((advance Q R c).work.families +
          (stabilize Q R fuel (advance Q R c).cache).work.families)
      nlinarith

theorem scan_candidates_le (Q : Optimizer H) (hL : 0 < L) (C : CutOracle G L hL)
    (R M : ℕ) (cells : Pair n → Fin L) (order : List (Pair n)) (c : Cache H) :
    (scan Q hL C R M cells order c).work.candidates ≤ n * n *
      (scan Q hL C R M cells order c).work.families := by
  induction order generalizing c with
  | nil => simp [scan]
  | cons p ps ih =>
      simp only [scan]
      split_ifs with h
      · have ha := refresh_candidates_le
          (sampleRound hL C c.state p (membership_of_flag c.state p h.2) (cells p))
        have hb := ih (refresh Q
          (sampleRound hL C c.state p (membership_of_flag c.state p h.2) (cells p)))
        simp only [Work.add, refreshWork, Nat.zero_add] at ha ⊢
        nlinarith
      · simp

theorem execute_candidates_le (Q : Optimizer H) (hL : 0 < L) (C : CutOracle G L hL)
    (R fuel : ℕ) (inputs : List (Input n L)) (c : Cache H) :
    (execute Q hL C R fuel inputs c).work.candidates ≤ n * n *
      (execute Q hL C R fuel inputs c).work.families := by
  induction inputs generalizing c with
  | nil => exact stabilize_candidates_le Q R fuel c
  | cons i inputs ih =>
      simp only [execute]
      split_ifs
      · exact stabilize_candidates_le Q R fuel c
      · have ha := stabilize_candidates_le Q R fuel c
        have hb := scan_candidates_le Q hL C R
          (stabilize Q R fuel c).cache.state.data.current i.cell i.order
          (stabilize Q R fuel c).cache
        have hd := ih (scan Q hL C R (stabilize Q R fuel c).cache.state.data.current
          i.cell i.order (stabilize Q R fuel c).cache).cache
        simp only [Work.add]
        nlinarith

theorem scan_tests_le (Q : Optimizer H) (hL : 0 < L) (C : CutOracle G L hL)
    (R M : ℕ) (cells : Pair n → Fin L) (order : List (Pair n)) (c : Cache H) :
    (scan Q hL C R M cells order c).work.epochTests ≤ order.length := by
  induction order generalizing c with
  | nil => simp [scan]
  | cons p ps ih =>
      simp only [scan]
      split_ifs
      · simpa only [Work.add, refreshWork, Nat.add_zero, List.length_cons,
          Nat.add_comm 1] using Nat.succ_le_succ (ih _)
      · simp

theorem execute_scale (Q : Optimizer H) (hL : 0 < L) (C : CutOracle G L hL)
    (R fuel : ℕ) (inputs : List (Input n L)) (c : Cache H) :
    (execute Q hL C R fuel inputs c).cache.state.data.scale =
      4 ^ (execute Q hL C R fuel inputs c).work.restarts * c.state.data.scale := by
  have h := (execute_trace Q hL C R fuel inputs c).scale_eq
  change ((_ : ℕ) : ℝ≥0) = 4 ^ _ * ((_ : ℕ) : ℝ≥0) at h
  exact_mod_cast h

theorem stabilize_remaining (Q : Optimizer H) (hL : 0 < L) (R fuel : ℕ)
    (c : Cache H) :
    (interpret (stabilize Q R fuel c).cache.state).remaining =
      (interpret c.state).remaining := by
  rw [stabilize_refines Q hL]
  exact selectedTrajectory_remaining P _ _ _

theorem trace_current_mass_le {r : ℝ≥0} (hr : 1 ≤ r)
    {s t : State G D (L : ℝ≥0)} {k q : ℕ} (h : Trace P r s k q t) :
    t.mass ≤ s.mass := by
  calc
    t.mass = 1 * t.mass := by simp
    _ ≤ r ^ k * t.mass := mul_le_mul_of_nonneg_right (one_le_pow₀ hr) zero_le
    _ ≤ s.mass := h.mass_bound

/-- Complete permutations are required exactly at epochs that execute. Their
data have already been supplied; this is only a proof-side legality condition. -/
def CompleteInputs (Q : Optimizer H) (hL : 0 < L) (C : CutOracle G L hL)
    (R fuel : ℕ) : List (Input n L) → Cache H → Prop
  | [], _ => True
  | i :: inputs, c =>
      let a := stabilize Q R fuel c
      if a.cache.optimal == 0 then True else
        i.order.Nodup ∧ i.order.toFinset = (interpret a.cache.state).remaining ∧
          CompleteInputs Q hL C R fuel inputs
            (scan Q hL C R a.cache.state.data.current i.cell i.order a.cache).cache

/-- With enough supplied complete epochs and geometric restart fuel, every
integer execution terminates at zero. No probabilistic success is assumed. -/
theorem execute_terminal (Q : Optimizer H) (hL : 0 < L) (C : CutOracle G L hL)
    (R fuel : ℕ) (hR : 1 < (R : ℝ≥0)) (inputs : List (Input n L)) (c : Cache H)
    (hfuel : (interpret c.state).mass < (R : ℝ≥0) ^ fuel)
    (hlen : (interpret c.state).remaining.card ≤ inputs.length)
    (hcomplete : CompleteInputs Q hL C R fuel inputs c) :
    (execute Q hL C R fuel inputs c).cache.optimal = 0 := by
  induction inputs generalizing c with
  | nil =>
      apply ((stabilize Q R fuel c).cache.zero_correct hL).mpr
      apply AdaptiveEpoch.optimum_eq_zero_of_remaining_empty
      rw [stabilize_remaining Q hL]
      exact Finset.card_eq_zero.mp (Nat.eq_zero_of_le_zero hlen)
  | cons i inputs ih =>
      simp only [execute]
      split_ifs with hz
      · simpa only [beq_iff_eq] using hz
      · have hc : i.order.Nodup ∧
            i.order.toFinset = (interpret (stabilize Q R fuel c).cache.state).remaining ∧
            CompleteInputs Q hL C R fuel inputs
              (scan Q hL C R (stabilize Q R fuel c).cache.state.data.current
                i.cell i.order (stabilize Q R fuel c).cache).cache := by
          simpa only [CompleteInputs, ite_eq_right hz] using hcomplete
        apply ih _ _ _ hc.2.2
        · have hstab := stabilize_trace Q hL R fuel c
          have hscan := scan_trace Q hL C R (stabilize Q R fuel c).cache.state.data.current
            i.cell i.order (stabilize Q R fuel c).cache
          exact (trace_current_mass_le hR.le (trace_trans P _ hstab hscan)).trans_lt hfuel
        · have hs := stabilize_eq_selectedStabilize Q hL R fuel hR c hfuel
          have hr : (interpret (stabilize Q R fuel c).cache.state).Ready (R : ℝ≥0) := by
            rw [hs]
            exact selectedStabilize_ready P _ hR _
          have hp : (interpret (stabilize Q R fuel c).cache.state).optimum ≠ 0 := by
            intro he
            apply hz
            simpa only [beq_iff_eq] using
              ((stabilize Q R fuel c).cache.zero_correct hL).mpr he
          have hprogress := AdaptiveEpoch.run_remaining_card_lt (R : ℝ≥0) hR.le
            (levels hL i) (interpret (stabilize Q R fuel c).cache.state) i.order hc.2.1 hr hp
          rw [← stabilize_remaining Q hL R fuel c] at hlen
          rw [scan_refines Q hL, ← interpret_mass]
          change (AdaptiveEpoch.run _ _ (levels hL i) _ _).state.remaining.card ≤ _
          simp only [List.length_cons] at hlen
          omega

theorem execute_valid (Q : Optimizer H) (hL : 0 < L) (C : CutOracle G L hL)
    (R fuel : ℕ) (hR : 1 < (R : ℝ≥0)) (inputs : List (Input n L)) (c : Cache H)
    (hfuel : (interpret c.state).mass < (R : ℝ≥0) ^ fuel)
    (hlen : (interpret c.state).remaining.card ≤ inputs.length)
    (hcomplete : CompleteInputs Q hL C R fuel inputs c) :
    IsIntegralCut G (cutSet (execute Q hL C R fuel inputs c).cache.state.data.cut)
      (D : Set (Pair n)) :=
  execute_zero_valid Q hL C R fuel inputs c
    (execute_terminal Q hL C R fuel hR inputs c hfuel hlen hcomplete)

/-- The deterministic branch recursion underlying the flexible law. Its
stabilizer is the exact first-ready state, rather than a fuel approximation. -/
noncomputable def selectedReference (hL : 0 < L) (R : ℕ) (hR : 1 < (R : ℝ≥0)) :
    List (Input n L) → State G D (L : ℝ≥0) → State G D (L : ℝ≥0)
  | [], s => s.selectedStabilize P (R : ℝ≥0) hR
  | i :: inputs, s =>
      let t := s.selectedStabilize P (R : ℝ≥0) hR
      if t.optimum = 0 then t else
        selectedReference hL R hR inputs
          (AdaptiveEpoch.run (R : ℝ≥0) t.mass (levels hL i) t i.order).state

theorem execute_refines_selectedReference (Q : Optimizer H) (hL : 0 < L)
    (C : CutOracle G L hL) (R fuel : ℕ) (hR : 1 < (R : ℝ≥0))
    (inputs : List (Input n L)) (c : Cache H)
    (hfuel : (interpret c.state).mass < (R : ℝ≥0) ^ fuel) :
    interpret (execute Q hL C R fuel inputs c).cache.state =
      selectedReference (H := H) hL R hR inputs (interpret c.state) := by
  induction inputs generalizing c with
  | nil => exact stabilize_eq_selectedStabilize Q hL R fuel hR c hfuel
  | cons i inputs ih =>
      simp only [execute, selectedReference]
      rw [← stabilize_eq_selectedStabilize Q hL R fuel hR c hfuel]
      split_ifs with h₁ h₂ h₂
      · rfl
      · exact (h₂ (((stabilize Q R fuel c).cache.zero_correct hL).mp
          (by simpa only [beq_iff_eq] using h₁))).elim
      · exact (h₁ (by simpa only [beq_iff_eq] using
          ((stabilize Q R fuel c).cache.zero_correct hL).mpr h₂)).elim
      · have hstab := stabilize_trace Q hL R fuel c
        have hscan := scan_trace Q hL C R (stabilize Q R fuel c).cache.state.data.current
          i.cell i.order (stabilize Q R fuel c).cache
        have hm := (trace_current_mass_le hR.le (trace_trans P _ hstab hscan)).trans_lt hfuel
        rw [ih _ hm, scan_refines Q hL, interpret_mass]
        rfl

theorem run_families (Q : Optimizer H) (hL : 0 < L) (C : CutOracle G L hL)
    (R fuel : ℕ) (inputs : List (Input n L)) (s : Code G D L) :
    (run Q hL C R fuel inputs s).work.families =
      1 + (run Q hL C R fuel inputs s).work.restarts +
        (run Q hL C R fuel inputs s).work.rounds := by
  simp only [run, start, Work.add, refreshWork, Nat.zero_add, execute_families]
  omega

theorem run_candidates_le (Q : Optimizer H) (hL : 0 < L) (C : CutOracle G L hL)
    (R fuel : ℕ) (inputs : List (Input n L)) (s : Code G D L) :
    (run Q hL C R fuel inputs s).work.candidates ≤
      n * n * (run Q hL C R fuel inputs s).work.families := by
  have ha := refresh_candidates_le s
  have hb := execute_candidates_le Q hL C R fuel inputs (refresh Q s)
  simp only [run, start, Work.add, refreshWork] at ha ⊢
  nlinarith

theorem run_valid (Q : Optimizer H) (hL : 0 < L) (C : CutOracle G L hL)
    (R fuel : ℕ) (hR : 1 < (R : ℝ≥0)) (inputs : List (Input n L)) (s : Code G D L)
    (hfuel : (interpret s).mass < (R : ℝ≥0) ^ fuel)
    (hlen : (interpret s).remaining.card ≤ inputs.length)
    (hcomplete : CompleteInputs Q hL C R fuel inputs (refresh Q s)) :
    IsIntegralCut G (cutSet (run Q hL C R fuel inputs s).cache.state.data.cut)
      (D : Set (Pair n)) :=
  execute_valid Q hL C R fuel hR inputs (refresh Q s) hfuel hlen hcomplete

end
end DirectedFlowCutGap.IntegerAdaptiveExecution
