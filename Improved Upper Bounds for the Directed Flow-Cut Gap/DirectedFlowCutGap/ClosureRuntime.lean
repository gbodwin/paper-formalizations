import DirectedFlowCutGap.TabulatedIntegralFlow
import DirectedFlowCutGap.CandidateClosureProvider

/-!
# Retained closure output and finite integer bounds

The final residual table is searched once. Its keys are materialized once, the
cut is converted once, and the closure is retained for subsequent decoding.
The output identity is with the concrete finite hooks of
`CandidateClosureProvider`, not merely with some minimum closure.
-/
namespace DirectedFlowCutGap.ClosureRuntime

open scoped BigOperators
open IntegralNetworkFlow IntegralNetworkFlow.Tabulated
open MinimumClosureProblem MinimumClosureCut MinimumClosureOptimizer

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- An ordinary membership scan, carrying the exact number of inspected cells. -/
def memberWithCost {K : Type*} [DecidableEq K] (k : K) : List K → Bool × ℕ
  | [] => (false,0)
  | a :: xs => if a = k then (true,1) else
      let r := memberWithCost k xs
      (r.1,r.2+1)

theorem memberWithCost_value {K : Type*} [DecidableEq K] (k : K) (xs : List K) :
    (memberWithCost k xs).1 = decide (k ∈ xs) := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    by_cases h : a = k
    · simp [memberWithCost, h]
    · simp [memberWithCost, h, Ne.symm h, ih]

theorem memberWithCost_bound {K : Type*} [DecidableEq K] (k : K) (xs : List K) :
    (memberWithCost k xs).2 ≤ xs.length := by
  induction xs with
  | nil => simp [memberWithCost]
  | cons a xs ih => by_cases h : a = k <;> simp [memberWithCost, h, ih]

/-- The actual complement conversion, including its membership-scan counter. -/
def absentWithCost (keys : List V) : List V → List V × ℕ
  | [] => ([],0)
  | v :: vs =>
      let a := memberWithCost v keys
      let b := absentWithCost keys vs
      (if a.1 then b.1 else v :: b.1, a.2+1+b.2)

omit [Fintype V] in
theorem absentWithCost_value (keys vs : List V) :
    (absentWithCost keys vs).1 = vs.filter fun v => !(decide (v ∈ keys)) := by
  induction vs with
  | nil => rfl
  | cons v vs ih =>
    simp only [absentWithCost, memberWithCost_value, ih, List.filter_cons]
    split <;> simp_all

omit [Fintype V] in
theorem absentWithCost_bound (keys vs : List V) :
    (absentWithCost keys vs).2 ≤ vs.length * (keys.length+1) := by
  induction vs with
  | nil => simp [absentWithCost]
  | cons v vs ih =>
    have h := memberWithCost_bound v keys
    simp only [absentWithCost, List.length_cons, Nat.add_mul, Nat.one_mul]
    omega

/-- A finite set from an already duplicate-free list; no deduplication search
is performed by this conversion. -/
def setOfNodup (xs : List V) (h : xs.Nodup) : Finset V := ⟨xs, h⟩

omit [Fintype V] [DecidableEq V] in
@[simp] theorem mem_setOfNodup (xs : List V) (h : xs.Nodup) (v : V) :
    v ∈ setOfNodup xs h ↔ v ∈ xs := Iff.rfl

/-- One residual-table run and one retained-key complement pass. -/
def finalCutWithCost (E : ResidualSearch.Enumeration V)
    {c : Capacity V} {s t : V} (f : Flow c s t) : Finset V × ℕ :=
  letI : DecidableRel f.residual.Adj := fun u v =>
    inferInstanceAs (Decidable (f.amount u v < (c u v : ℤ)))
  let a := ResidualSearch.searchTable E f.residual t
  let keys := a.1.entries.map Sigma.fst
  let b := absentWithCost keys E.vertices
  (setOfNodup b.1 (by rw [absentWithCost_value]; exact E.nodup.filter _),
    a.2 + keys.length + b.2 + b.1.length)

theorem finalCutWithCost_value (E : ResidualSearch.Enumeration V)
    {c : Capacity V} {s t : V} (f : Flow c s t) :
    (finalCutWithCost E f).1 = finiteResidualCut E f := by
  ext v
  simp [finalCutWithCost, absentWithCost_value, finiteResidualCut,
    ResidualSearch.separatingCut, ResidualSearch.keys, E.complete]
  rfl

theorem finalCutWithCost_bound (E : ResidualSearch.Enumeration V)
    {c : Capacity V} {s t : V} (f : Flow c s t) :
    (finalCutWithCost E f).2 ≤ 2*(Fintype.card V)^3 +
      Fintype.card V * (Fintype.card V+1) + 2*Fintype.card V := by
  let : DecidableRel f.residual.Adj := fun u v =>
    inferInstanceAs (Decidable (f.amount u v < (c u v : ℤ)))
  have hs := ResidualSearch.searchTable_count_le (G := f.residual) (t := t) E
  have hk := (ResidualSearch.searchTable E f.residual t).1.length_le_card
  have ha := absentWithCost_bound
    ((ResidualSearch.searchTable E f.residual t).1.entries.map Sigma.fst) E.vertices
  rw [List.length_map, E.length_eq_card] at ha
  have hb : (absentWithCost
      ((ResidualSearch.searchTable E f.residual t).1.entries.map Sigma.fst) E.vertices).1.length ≤
      Fintype.card V := by
    rw [absentWithCost_value, ← E.length_eq_card]
    exact List.length_filter_le _ _
  have hm := Nat.mul_le_mul_left (Fintype.card V) (Nat.add_le_add_right hk 1)
  have hsum := Nat.add_le_add (Nat.add_le_add (Nat.add_le_add hs hk) (ha.trans hm)) hb
  convert hsum using 1
  · simp only [finalCutWithCost, List.length_map]
    rfl
  · omega

/-- The retained capacity table has the same exact capacities. -/
def retainedCapacity (E : ResidualSearch.Enumeration V) (c : Capacity V) : Capacity V :=
  let cells := FlowTable.dense E fun u v => (c u v : ℤ)
  fun u v => (read (u,v) cells).1.toNat

omit [Fintype V] in
theorem retainedCapacity_eq (E : ResidualSearch.Enumeration V) (c : Capacity V) :
    retainedCapacity E c = c := by
  funext u v
  simp [retainedCapacity, FlowTable.read_dense]

section Closure
variable {A : Type*} [Fintype A] [DecidableEq A]

/-- A single run returns one retained flow table, followed by one final cut. -/
def solve (P : Problem A) (E : ResidualSearch.Enumeration (Vertex A)) :
    Finset A × ℕ :=
  let c := retainedCapacity E (capacity P)
  let initial := FlowTable.materialize E (Flow.zero c source sink)
  let r := FlowTable.runWithCost E initial (budget P)
  let cut := finalCutWithCost E r.1.asFlow
  (cores cut.1, initial.cells.length + r.2 + cut.2)

/-- Exact equality with the frozen provider's concrete closure output. -/
theorem solve_value (P : Problem A) (E : ResidualSearch.Enumeration (Vertex A)) :
    (solve P E).1 = CandidateClosureProvider.closureSet P
      (CandidateClosureProvider.finiteHooks P E) := by
  simp only [solve, finalCutWithCost_value,
    FlowTable.runWithCost_table, FlowTable.run_refines, FlowTable.materialize_asFlow,
    CandidateClosureProvider.closureSet, CandidateClosureProvider.finiteHooks,
    MinimumClosureOptimizer.runFlow]
  rw [retainedCapacity_eq]

theorem solve_optimal (P : Problem A) (E : ResidualSearch.Enumeration (Vertex A))
    (hfeas : ∃ T, P.IsClosed T) :
    P.IsClosed (solve P E).1 ∧ ∀ T, P.IsClosed T → P.objective (solve P E).1 ≤ P.objective T := by
  rw [solve_value]
  exact CandidateClosureProvider.closureSet_optimal P _ hfeas

/-- Conservative charge for the parts instrumented above. The final term
includes the final search and complement conversion, not another optimizer call. -/
def closureCharge (N B : ℕ) : ℕ :=
  N^2 + B * FlowTable.stepCharge N (N^2) + 2*N^3 + N*(N+1) + 2*N

theorem solve_charge_bound (P : Problem A) (E : ResidualSearch.Enumeration (Vertex A)) :
    (solve P E).2 ≤ closureCharge (Fintype.card (Vertex A)) (budget P) := by
  have hr := FlowTable.runWithCost_bound E
    (FlowTable.materialize E (Flow.zero (retainedCapacity E (capacity P)) source sink)) (budget P)
  have hf := finalCutWithCost_bound E
    (FlowTable.runWithCost E
      (FlowTable.materialize E (Flow.zero (retainedCapacity E (capacity P)) source sink))
      (budget P)).1.asFlow
  have hi : (FlowTable.materialize E
      (Flow.zero (retainedCapacity E (capacity P)) source sink)).cells.length =
      (Fintype.card (Vertex A))^2 := FlowTable.dense_length E _
  rw [hi] at hr
  simp only [solve]
  rw [hi]
  unfold closureCharge
  omega

/-- General signed closure capacities include the sign-cost and a barrier.
This safe bound does not assume those two summands are disjoint. -/
theorem capacity_le_twice_budget (P : Problem A) (u v : Vertex A) :
    capacity P u v ≤ 2*budget P+1 := by
  have ha (a : A) : (P.cost a).natAbs ≤ budget P :=
    Finset.single_le_sum (f := fun a => (P.cost a).natAbs)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ a)
  have hp (a : A) : positive P a ≤ budget P := by
    apply le_trans _ (ha a)
    rw [positive, ← Int.toNat_add_toNat_neg_eq_natAbs]
    exact Nat.le_add_right _ _
  have hn (a : A) : negative P a ≤ budget P := by
    apply le_trans _ (ha a)
    rw [negative, ← Int.toNat_add_toNat_neg_eq_natAbs]
    exact Nat.le_add_left _ _
  cases u with
  | inl a =>
    cases v with
    | inl b => simp only [capacity, barrier]; split <;> omega
    | inr b =>
      cases b with
      | false => simp [capacity]
      | true =>
        have := hp a
        simp only [capacity, barrier]
        split <;> omega
  | inr b =>
    cases b with
    | true => cases v <;> simp [capacity]
    | false =>
      cases v with
      | inl a =>
        have := hn a
        simp only [capacity, barrier]
        split <;> omega
      | inr b => cases b <;> simp [capacity]

end Closure
section Candidates
open CandidatePortDifferenceSystem CandidateThresholdClosure CandidateGridOptimizer
open CandidateGridRounding.DifferenceSystem CandidateClosureProvider

/-- Compute the closure once, then retain all integer vertex numerators in the
supplied vertex order. The decoded function closes only over the saved closure. -/
def candidateNumerators (G : Digraph V) [DecidableRel G.Adj]
    (s t : V) (X : Finset V) (L B : ℕ) (hL : 0 < L)
    (EV : ResidualSearch.Enumeration V)
    (E : ResidualSearch.Enumeration (Vertex (Node (Point V) L)))
    (hfeas : CandidateFeasible G s t X L B) : List (V × ℤ) :=
  let P := candidateClosure G s t X L B
  let r := solve P E
  let hc := (solve_optimal P E (closure_nonempty (system G s t X L B)
    (integerCosts X) (system_nonempty G s t X L B hL hfeas))).1
  let q := decode (system G s t X L B) (integerCosts X) r.1 hc
  EV.vertices.map fun v => (v, if v ∈ X then (L : ℤ) else
    ((q (TerminalPorts.core v, true) : ℕ) : ℤ) - (q (TerminalPorts.core v, false) : ℕ))

/-- Every entry equals the very same deterministic provider numerator. -/
theorem candidateNumerators_value (G : Digraph V) [DecidableRel G.Adj]
    (s t : V) (X : Finset V) (L B : ℕ) (hL : 0 < L)
    (EV : ResidualSearch.Enumeration V)
    (E : ResidualSearch.Enumeration (Vertex (Node (Point V) L)))
    (hfeas : CandidateFeasible G s t X L B) :
    candidateNumerators G s t X L B hL EV E hfeas = EV.vertices.map fun v =>
      (v, candidateNumerator G s t X L B hL
        (finiteHooks (candidateClosure G s t X L B) E) hfeas v) := by
  have hd (S : CandidateGridRounding.DifferenceSystem (Point V) L)
      (c : Point V → ℤ) (T U : Finset (Node (Point V) L))
      (hT : (problem S c).IsClosed T) (hU : (problem S c).IsClosed U) (h : T = U) :
      decode S c T hT = decode S c U hU := by
    subst U
    rfl
  let hf := closure_nonempty (system G s t X L B) (integerCosts X)
    (system_nonempty G s t X L B hL hfeas)
  have hq := hd (system G s t X L B) (integerCosts X)
    (solve (candidateClosure G s t X L B) E).1
    (closureSet (candidateClosure G s t X L B)
      (finiteHooks (candidateClosure G s t X L B) E))
    (solve_optimal (candidateClosure G s t X L B) E hf).1
    (closureSet_optimal (candidateClosure G s t X L B)
      (finiteHooks (candidateClosure G s t X L B) E) hf).1
    (solve_value (candidateClosure G s t X L B) E)
  unfold candidateNumerators candidateNumerator candidateGrid gridPoint
  dsimp only
  simp only [hq]
  rfl

theorem candidateNumerators_read (G : Digraph V) [DecidableRel G.Adj]
    (s t : V) (X : Finset V) (L B : ℕ) (hL : 0 < L)
    (EV : ResidualSearch.Enumeration V)
    (E : ResidualSearch.Enumeration (Vertex (Node (Point V) L)))
    (hfeas : CandidateFeasible G s t X L B) (v : V) :
    (read v (candidateNumerators G s t X L B hL EV E hfeas)).1 =
      candidateNumerator G s t X L B hL
        (finiteHooks (candidateClosure G s t X L B) E) hfeas v := by
  rw [candidateNumerators_value]
  apply read_eq_of_cells _ _ ?_ v ?_
  · intro a z h
    obtain ⟨u, _, hu⟩ := List.mem_map.mp h
    cases hu
    rfl
  · exact List.mem_map.mpr ⟨(v, candidateNumerator G s t X L B hL
      (finiteHooks (candidateClosure G s t X L B) E) hfeas v),
      List.mem_map.mpr ⟨v, EV.complete v, rfl⟩, rfl⟩

theorem candidateNumerators_length (G : Digraph V) [DecidableRel G.Adj]
    (s t : V) (X : Finset V) (L B : ℕ) (hL : 0 < L)
    (EV : ResidualSearch.Enumeration V)
    (E : ResidualSearch.Enumeration (Vertex (Node (Point V) L)))
    (hfeas : CandidateFeasible G s t X L B) :
    (candidateNumerators G s t X L B hL EV E hfeas).length = Fintype.card V := by
  rw [candidateNumerators_value, List.length_map, EV.length_eq_card]

/-- The numerical augmentation budget is polynomial for these concrete
instances when the chosen integer threshold is at most the vertex count. -/
theorem candidate_budget_polynomial (G : Digraph V) [DecidableRel G.Adj]
    (s t : V) (X : Finset V) (L B : ℕ) (hL : L ≤ Fintype.card V) :
    budget (candidateClosure G s t X L B) ≤
      6*Fintype.card V*(Fintype.card V+1) := by
  exact (candidate_budget_le G s t X L B).trans
    (Nat.mul_le_mul_left (6*Fintype.card V) (Nat.add_le_add_right hL 1))

theorem candidate_capacity_polynomial (G : Digraph V) [DecidableRel G.Adj]
    (s t : V) (X : Finset V) (L B : ℕ) (hL : L ≤ Fintype.card V)
    (u v : Vertex (Node (Point V) L)) :
    capacity (candidateClosure G s t X L B) u v ≤
      12*Fintype.card V*(Fintype.card V+1)+1 := by
  have hc := capacity_le_twice_budget (candidateClosure G s t X L B) u v
  have hb := candidate_budget_polynomial G s t X L B hL
  nlinarith

/-- Binary storage bound for every cell of every feasible retained flow in the
actual candidate network. The arbitrary epoch scale B does not enter it. -/
theorem candidate_flow_bits (G : Digraph V) [DecidableRel G.Adj]
    (s t : V) (X : Finset V) (L B : ℕ) (hL : L ≤ Fintype.card V)
    (T : FlowTable (capacity (candidateClosure G s t X L B)) source sink)
    (e : Vertex (Node (Point V) L) × Vertex (Node (Point V) L)) (z : ℤ)
    (hz : (e,z) ∈ T.cells) :
    1+Nat.size z.natAbs ≤ 1+Nat.size (12*Fintype.card V*(Fintype.card V+1)+1) :=
  T.cell_signed_bits_le _ (candidate_capacity_polynomial G s t X L B hL) e z hz

end Candidates
end DirectedFlowCutGap.ClosureRuntime
