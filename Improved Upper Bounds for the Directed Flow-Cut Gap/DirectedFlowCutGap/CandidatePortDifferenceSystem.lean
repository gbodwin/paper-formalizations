import DirectedFlowCutGap.CandidateGridOptimizer
import DirectedFlowCutGap.CandidateThresholdClosure

/-!
# The actual endpoint-safe candidate constraints as a finite integer system

This is the explicit input transformation for threshold closure. It preserves
all port pins, zero port gaps, outside caps, and the signed objective. Graph
adjacency is supplied with an actual decision procedure; no real comparison is
needed to build the finite integer constraint data.
-/
namespace DirectedFlowCutGap.CandidatePortDifferenceSystem

open scoped BigOperators
open CandidateGridRounding CandidateGridRounding.DifferenceSystem
open CandidateGridOptimizer CandidateThresholdClosure

variable {V : Type*} [Fintype V] [DecidableEq V]

@[instance_reducible] def decidablePortAdj (G : Digraph V) [DecidableRel G.Adj] :
    DecidableRel (TerminalPorts.graph G).Adj := by
  intro a b
  rcases a with a | a <;> rcases b with b | b
  · exact inferInstanceAs (Decidable (G.Adj a b))
  · cases b <;> dsimp [TerminalPorts.graph] <;> infer_instance
  · cases a <;> dsimp [TerminalPorts.graph] <;> infer_instance
  · cases a <;> cases b <;> dsimp [TerminalPorts.graph] <;> infer_instance

attribute [local instance] decidablePortAdj

def portCap (X : Finset V) (L B : ℕ) : TerminalPorts.Vertex V → ℕ
  | .inl v => if v ∈ X then L else B
  | .inr _ => 0

def orderBound (L : ℕ) (a b : Point V) : ℤ :=
  if a.1 = b.1 ∧ a.2 = false ∧ b.2 = true then 0 else L

def gapBound (X : Finset V) (L B : ℕ) (a b : Point V) : ℤ :=
  if a.1 = b.1 ∧ a.2 = true ∧ b.2 = false then portCap X L B a.1 else L

def edgeBound (G : Digraph V) [DecidableRel G.Adj] (L : ℕ) (a b : Point V) : ℤ :=
  if a.2 = false ∧ b.2 = true ∧ (TerminalPorts.graph G).Adj b.1 a.1 then 0 else L

/-- Default difference bounds L are vacuous on [0,L]. Taking minima intersects
all three families of constraints, including coincident/self edges. -/
def system (G : Digraph V) [DecidableRel G.Adj] (s t : V) (X : Finset V) (L B : ℕ) :
    DifferenceSystem (Point V) L where
  lower := fun a => if a.1 = TerminalPorts.sink t then ⟨L, Nat.lt_succ_self _⟩ else 0
  upper := fun a => if a.1 = TerminalPorts.source s then 0 else ⟨L, Nat.lt_succ_self _⟩
  bound := fun a b => min (orderBound L a b)
    (min (gapBound X L B a b) (edgeBound G L a b))

omit [Fintype V] in
private theorem bound_le_order (G : Digraph V) [DecidableRel G.Adj]
    (s t : V) (X : Finset V) (L B : ℕ) (a b : Point V) :
    (system G s t X L B).bound a b ≤ orderBound L a b := min_le_left _ _

omit [Fintype V] in
private theorem bound_le_gap (G : Digraph V) [DecidableRel G.Adj]
    (s t : V) (X : Finset V) (L B : ℕ) (a b : Point V) :
    (system G s t X L B).bound a b ≤ gapBound X L B a b :=
  (min_le_right _ _).trans (min_le_left _ _)

omit [Fintype V] in
private theorem bound_le_edge (G : Digraph V) [DecidableRel G.Adj]
    (s t : V) (X : Finset V) (L B : ℕ) (a b : Point V) :
    (system G s t X L B).bound a b ≤ edgeBound G L a b :=
  (min_le_right _ _).trans (min_le_right _ _)

omit [Fintype V] in
theorem system_feasible_of_ports (G : Digraph V) [DecidableRel G.Adj]
    (s t : V) (X : Finset V) (L B : ℕ) {p : Point V → ℝ}
    (hp : CandidateGridOptimizer.Feasible G s t X L B p) :
    (system G s t X L B).Feasible p := by
  have hsource (b : Bool) : p (TerminalPorts.source s, b) = 0 := by
    cases b
    · exact hp.source
    · exact (hp.ports (.inl s)).trans hp.source
  have hsink (b : Bool) : p (TerminalPorts.sink t, b) = (L : ℝ) := by
    cases b
    · exact (hp.ports (.inr t)).symm.trans hp.sink
    · exact hp.sink
  have hbox (a b : Point V) : p a - p b ≤ (L : ℝ) := by
    have ha := (hp.bounded a).2
    have hb := (hp.bounded b).1
    linarith
  have hgap (v : TerminalPorts.Vertex V) :
      after p v - before p v ≤ (portCap X L B v : ℝ) := by
    cases v with
    | inl v =>
      by_cases hv : v ∈ X
      · simpa [portCap, hv, before, after] using hbox (TerminalPorts.core v, true) (TerminalPorts.core v, false)
      · simpa [portCap, hv] using hp.outsideCap v hv
    | inr a => simp [portCap, hp.ports a]
  refine ⟨?_, ?_⟩
  · rintro ⟨v, b⟩
    constructor
    · by_cases hv : v = TerminalPorts.sink t
      · subst v
        simpa [system] using (hsink b).ge
      · simpa [system, hv] using (hp.bounded (v, b)).1
    · by_cases hv : v = TerminalPorts.source s
      · subst v
        simpa [system] using (hsource b).le
      · simpa [system, hv] using (hp.bounded (v, b)).2
  · intro a b
    change p a - p b ≤ ((min (orderBound L a b)
      (min (gapBound X L B a b) (edgeBound G L a b)) : ℤ) : ℝ)
    rw [Int.cast_min, Int.cast_min]
    refine le_min ?_ (le_min ?_ ?_)
    · by_cases h : a.1 = b.1 ∧ a.2 = false ∧ b.2 = true
      · rw [orderBound, ite_eq_left h, Int.cast_zero]
        have ha : a = (a.1, false) := Prod.ext rfl h.2.1
        have hb : b = (a.1, true) := Prod.ext h.1.symm h.2.2
        rw [ha, hb]
        exact sub_nonpos.mpr (hp.ordered a.1)
      · simpa [orderBound, h] using hbox a b
    · by_cases h : a.1 = b.1 ∧ a.2 = true ∧ b.2 = false
      · rw [gapBound, ite_eq_left h]
        have ha : a = (a.1, true) := Prod.ext rfl h.2.1
        have hb : b = (a.1, false) := Prod.ext h.1.symm h.2.2
        rw [ha, hb]
        exact_mod_cast hgap a.1
      · simpa [gapBound, h] using hbox a b
    · by_cases h : a.2 = false ∧ b.2 = true ∧ (TerminalPorts.graph G).Adj b.1 a.1
      · rw [edgeBound, ite_eq_left h, Int.cast_zero]
        have ha : a = (a.1, false) := Prod.ext rfl h.1
        have hb : b = (b.1, true) := Prod.ext rfl h.2.1
        rw [ha, hb]
        exact sub_nonpos.mpr (hp.edge b.1 a.1 h.2.2)
      · simpa [edgeBound, h] using hbox a b

omit [Fintype V] in
theorem ports_feasible_of_system (G : Digraph V) [DecidableRel G.Adj]
    (s t : V) (X : Finset V) (L B : ℕ) {p : Point V → ℝ}
    (hp : (system G s t X L B).Feasible p) :
    CandidateGridOptimizer.Feasible G s t X L B p := by
  have hbounded (a : Point V) : 0 ≤ p a ∧ p a ≤ (L : ℝ) := by
    have hlow : (0 : ℝ) ≤ ((system G s t X L B).lower a : ℝ) := Nat.cast_nonneg _
    have hupp : ((system G s t X L B).upper a : ℝ) ≤ (L : ℝ) := by
      exact_mod_cast Nat.le_of_lt_succ ((system G s t X L B).upper a).isLt
    exact ⟨hlow.trans (hp.1 a).1, (hp.1 a).2.trans hupp⟩
  have hordered (v : TerminalPorts.Vertex V) : before p v ≤ after p v := by
    have h := (hp.2 (v, false) (v, true)).trans
      (Int.cast_le.mpr (bound_le_order G s t X L B (v, false) (v, true)))
    simpa [orderBound, before, after] using h
  have hgap (v : TerminalPorts.Vertex V) :
      after p v - before p v ≤ (portCap X L B v : ℝ) := by
    have h := (hp.2 (v, true) (v, false)).trans
      (Int.cast_le.mpr (bound_le_gap G s t X L B (v, true) (v, false)))
    simpa [gapBound, before, after] using h
  refine ⟨hbounded, hordered, ?_, ?_, ?_, ?_, ?_⟩
  · have hu : p (TerminalPorts.source s, false) ≤ 0 := by
      simpa [system] using (hp.1 (TerminalPorts.source s, false)).2
    exact le_antisymm hu (hbounded (TerminalPorts.source s, false)).1
  · have hl : (L : ℝ) ≤ p (TerminalPorts.sink t, true) := by
      simpa [system] using (hp.1 (TerminalPorts.sink t, true)).1
    exact le_antisymm (hbounded (TerminalPorts.sink t, true)).2 hl
  · intro a
    have hg := hgap (.inr a)
    have ho := hordered (.inr a)
    simp only [portCap, Nat.cast_zero] at hg
    exact le_antisymm (sub_nonpos.mp hg) ho
  · intro v hv
    simpa [portCap, hv] using hgap (TerminalPorts.core v)
  · intro u v huv
    have h := (hp.2 (v, false) (u, true)).trans
      (Int.cast_le.mpr (bound_le_edge G s t X L B (v, false) (u, true)))
    simpa [edgeBound, before, after, huv] using h

omit [Fintype V] in
theorem system_feasible_iff (G : Digraph V) [DecidableRel G.Adj]
    (s t : V) (X : Finset V) (L B : ℕ) (p : Point V → ℝ) :
    (system G s t X L B).Feasible p ↔ CandidateGridOptimizer.Feasible G s t X L B p :=
  ⟨ports_feasible_of_system G s t X L B, system_feasible_of_ports G s t X L B⟩

/-- Only -1, 0, and 1 occur in the actual unit-cost candidate objective. -/
def integerCosts (X : Finset V) : Point V → ℤ
  | (.inl v, b) => if v ∈ X then 0 else if b then 1 else -1
  | (.inr _, _) => 0

omit [Fintype V] in
theorem integerCosts_coe (X : Finset V) :
    (fun a => (integerCosts X a : ℝ)) = costs X := by
  funext ⟨v, b⟩
  cases v with
  | inl v => by_cases hv : v ∈ X <;> cases b <;> simp [integerCosts, costs, hv]
  | inr a => simp [integerCosts, costs]

omit [Fintype V] in
theorem integerCosts_abs_le (X : Finset V) (a : Point V) : (integerCosts X a).natAbs ≤ 1 := by
  rcases a with ⟨v, b⟩
  cases v with
  | inl v => by_cases hv : v ∈ X <;> cases b <;> simp [integerCosts, hv]
  | inr a => simp [integerCosts]

omit [DecidableEq V] in
/-- There are exactly six split-potential coordinates per original vertex. -/
theorem card_point : Fintype.card (Point V) = 6 * Fintype.card V := by
  simp [Point, TerminalPorts.Vertex, Fintype.card_prod, Fintype.card_sum]
  omega

/-- The actual threshold-closure instance, constructed using only finite graph
adjacency, membership, and integer arithmetic. -/
def candidateClosure (G : Digraph V) [DecidableRel G.Adj]
    (s t : V) (X : Finset V) (L B : ℕ) : MinimumClosureProblem.Problem (Node (Point V) L) :=
  problem (system G s t X L B) (integerCosts X)

theorem candidateClosure_cost_budget (G : Digraph V) [DecidableRel G.Adj]
    (s t : V) (X : Finset V) (L B : ℕ) :
    (∑ a : Node (Point V) L, ((candidateClosure G s t X L B).cost a).natAbs) ≤
      6 * Fintype.card V * (L + 1) := by
  simpa only [candidateClosure, card_point, mul_one] using
    absolute_cost_le (system G s t X L B) (integerCosts X) 1 (integerCosts_abs_le X)

end DirectedFlowCutGap.CandidatePortDifferenceSystem
