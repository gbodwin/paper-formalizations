import DirectedFlowCutGap.FlexibleClosureRounding
import DirectedFlowCutGap.IntegerEpochParameters
import DirectedFlowCutGap.ClosureRuntime
import DirectedFlowCutGap.IntegerLevelCuts
import Mathlib.Data.Vector.Basic

/-!
# Retained integer data for the adaptive algorithm

`Vector` is Lean's sized `Array`, not a function encoding. The executable data
below consists only of natural numbers and Boolean arrays. Its interpretation
and certificates are separate. In particular a cached candidate is a stored
matrix, and reading its mass or installing it never invokes an optimizer.

The optimizer and shortest-path adapters are explicit interfaces. Their
certificates concern the exact returned arrays; operation bounds for their
implementations are deliberately not postulated here.
-/
namespace DirectedFlowCutGap.RetainedGridState
open scoped BigOperators NNReal
open CandidateSchedule CandidateOptimization EpochAccounting
open FlexibleCandidateSchedule FlexibleGridProvider
open IntegralNetworkFlow

abbrev Pair (n : ℕ) := Fin n × Fin n
abbrev Flags (n : ℕ) := Vector Bool n
abbrev PairFlags (n : ℕ) := Vector (Flags n) n
abbrev Row (n : ℕ) := Vector ℕ n
abbrev Family (n : ℕ) := Vector (Vector (Row n) n) n

def row {n : ℕ} (a : Family n) (p : Pair n) : Row n := a[p.1.val][p.2.val]
def flag {n : ℕ} (a : PairFlags n) (p : Pair n) : Bool := a[p.1.val][p.2.val]

def cutSet {n : ℕ} (a : Flags n) : Finset (Fin n) :=
  Finset.univ.filter fun v => a[v.val] = true

def remainingSet {n : ℕ} (a : PairFlags n) : Finset (Pair n) :=
  Finset.univ.filter fun p => flag a p = true

def massNumerator {n : ℕ} (a : PairFlags n) (x : Flags n) (w : Family n) : ℕ :=
  ∑ p ∈ remainingSet a, ∑ v ∈ Finset.univ.filter (fun v : Fin n => x[v.val] = false),
    (row w p)[v.val]

/-- All runtime fields have finite integer encodings. `current` is retained. -/
structure Data (n : ℕ) where
  remaining : PairFlags n
  cut : Flags n
  weights : Family n
  scale : ℕ
  current : ℕ
deriving Repr, DecidableEq

def Data.install {n : ℕ} (s : Data n) (w : Family n) (m : ℕ) : Data n :=
  { s with weights := w, scale := 4 * s.scale, current := m }

/-- Erase precisely the original label, including when an endpoint is cut. -/
def eraseFlag {n : ℕ} (a : PairFlags n) (p : Pair n) : PairFlags n :=
  Vector.ofFn fun s => Vector.ofFn fun t =>
    if (s, t) = p then false else flag a (s, t)

def unionFlags {n : ℕ} (x y : Flags n) : Flags n :=
  Vector.ofFn fun v => x[v.val] || y[v.val]

/-- This operation freezes the actual weights and recomputes the mass once. -/
def Data.round {n : ℕ} (s : Data n) (p : Pair n) (y : Flags n) : Data n :=
  let a := eraseFlag s.remaining p
  let x := unionFlags s.cut y
  { s with remaining := a, cut := x, current := massNumerator a x s.weights }

@[simp] theorem mem_cutSet {n : ℕ} (x : Flags n) (v : Fin n) :
    v ∈ cutSet x ↔ x[v.val] = true := by simp [cutSet]

@[simp] theorem mem_remainingSet {n : ℕ} (a : PairFlags n) (p : Pair n) :
    p ∈ remainingSet a ↔ flag a p = true := by simp [remainingSet]

@[simp] theorem remainingSet_eraseFlag {n : ℕ} (a : PairFlags n) (p : Pair n) :
    remainingSet (eraseFlag a p) = (remainingSet a).erase p := by
  ext q
  simp only [mem_remainingSet, flag, eraseFlag, Vector.getElem_ofFn,
    Finset.mem_erase]
  by_cases h : q = p <;> simp [h]

@[simp] theorem cutSet_unionFlags {n : ℕ} (x y : Flags n) :
    cutSet (unionFlags x y) = cutSet x ∪ cutSet y := by
  ext v
  simp [unionFlags]

section
variable {n L : ℕ} {G : Digraph (Fin n)} {D : Finset (Pair n)}

noncomputable def weights (L : ℕ) (w : Family n) (p : Pair n) (v : Fin n) : ℝ≥0 :=
  ((row w p)[v.val] : ℝ≥0) / L

/-- This proposition contains no runtime state or optimization witness. -/
structure Valid (G : Digraph (Fin n)) (D : Finset (Pair n)) (L : ℕ)
    (s : Data n) : Prop where
  remaining_subset : remainingSet s.remaining ⊆ D
  feasible : ∀ p ∈ remainingSet s.remaining, IsFractionalCut G (weights L s.weights p) {p}
  cap : ∀ p ∈ remainingSet s.remaining, ∀ v ∉ cutSet s.cut,
    weights L s.weights p v ≤ (s.scale : ℝ≥0) / L
  processed : ∀ p ∈ D, p ∉ remainingSet s.remaining → CutsPair G (cutSet s.cut) p.1 p.2
  current_eq : s.current = massNumerator s.remaining s.cut s.weights

/-- Integer data plus an erased proof. There is no stored real-valued state. -/
structure Code (G : Digraph (Fin n)) (D : Finset (Pair n)) (L : ℕ) where
  data : Data n
  valid : Valid G D L data

noncomputable def interpret (s : Code G D L) : State G D (L : ℝ≥0) where
  remaining := remainingSet s.data.remaining
  cut := cutSet s.data.cut
  weight := weights L s.data.weights
  scale := s.data.scale
  remaining_subset := s.valid.remaining_subset
  feasible := s.valid.feasible
  cap := s.valid.cap
  processed := s.valid.processed

theorem membership_of_flag (s : Code G D L) (p : Pair n)
    (h : flag s.data.remaining p = true) : p ∈ (interpret s).remaining :=
  (mem_remainingSet s.data.remaining p).mpr h

theorem state_ext (s t : State G D (L : ℝ≥0))
    (ha : s.remaining = t.remaining) (hx : s.cut = t.cut)
    (hw : s.weight = t.weight) (hb : s.scale = t.scale) : s = t := by
  cases s
  cases t
  cases ha
  cases hx
  cases hw
  cases hb
  rfl

theorem massNumerator_eq (a : PairFlags n) (x : Flags n) (w : Family n) :
    familyMass (remainingSet a) (cutSet x) (weights L w) =
      (massNumerator a x w : ℝ≥0) / L := by
  simp only [familyMass, outsideMass, weights, massNumerator, Nat.cast_sum,
    Finset.sum_div, mem_cutSet, Bool.not_eq_true]

theorem interpret_mass (s : Code G D L) :
    (interpret s).mass = (s.data.current : ℝ≥0) / L := by
  rw [s.valid.current_eq]
  exact massNumerator_eq _ _ _

theorem interpret_naturalScale (s : Code G D L) : NaturalScale (interpret s) :=
  ⟨s.data.scale, rfl⟩

/-- The representation has integer weights even at deleted endpoints. -/
theorem interpret_allWeightsOnGrid (s : Code G D L) : AllWeightsOnGrid (interpret s) := by
  intro p _ v
  exact ⟨(row s.data.weights p)[v.val], rfl⟩

/-- Recover a validity certificate from equality of the four interpreted data
fields. This transports proofs only; it never extracts runtime data. -/
theorem valid_of_state (s : Data n) (t : State G D (L : ℝ≥0))
    (ha : remainingSet s.remaining = t.remaining) (hx : cutSet s.cut = t.cut)
    (hw : weights L s.weights = t.weight) (hb : (s.scale : ℝ≥0) = t.scale)
    (hm : s.current = massNumerator s.remaining s.cut s.weights) : Valid G D L s := by
  constructor
  · simpa only [ha] using t.remaining_subset
  · simpa only [ha, hw] using t.feasible
  · simpa only [ha, hx, hw, hb] using t.cap
  · simpa only [ha, hx] using t.processed
  · exact hm

/-- A predicate and its existence proof are erased by code generation. This
keeps the mathematical family provider out of executable call arguments. -/
noncomputable def selectedProvider
    {selector : FamilyProvider G D (L : ℝ≥0) → Prop}
    (H : ∃ P, selector P) : FamilyProvider G D (L : ℝ≥0) := Classical.choose H

theorem providerWitness (P : FamilyProvider G D (L : ℝ≥0)) : ∃ Q, Q = P := ⟨P, rfl⟩

@[simp] theorem selectedProvider_eq (P : FamilyProvider G D (L : ℝ≥0)) :
    selectedProvider (providerWitness P) = P := Classical.choose_spec (providerWitness P)

variable {selector : FamilyProvider G D (L : ℝ≥0) → Prop}

/-- A selected family retained once, with its exact integer objective. -/
structure Cache (H : ∃ P, selector P) where
  state : Code G D L
  candidate : Family n
  optimal : ℕ
  candidate_eq : weights L candidate = (selectedProvider H).family (interpret state)
  optimal_eq : optimal = massNumerator state.data.remaining state.data.cut candidate

namespace Cache
variable {H : ∃ P, selector P}

def massCode (c : Cache H) : MassCode (interpret c.state) where
  current := c.state.data.current
  optimal := c.optimal
  current_eq := interpret_mass c.state
  optimal_eq := by
    rw [← (selectedProvider H).objective_eq, ← c.candidate_eq, c.optimal_eq]
    exact massNumerator_eq _ _ _

def ready (R : ℕ) (c : Cache H) : Bool :=
  readyCode R c.state.data.current c.optimal

theorem ready_correct (hL : 0 < L) (R : ℕ) (c : Cache H) :
    c.ready R = true ↔ (interpret c.state).Ready (R : ℝ≥0) :=
  readyCode_correct hL R _ c.massCode

theorem zero_correct (hL : 0 < L) (c : Cache H) :
    c.optimal = 0 ↔ (interpret c.state).optimum = 0 := by
  simpa only [Nat.beq_eq, massCode] using zeroCode_correct hL _ c.massCode

/-- Install the already stored matrix. This function makes zero solver calls. -/
def install (c : Cache H) : Code G D L where
  data := c.state.data.install c.candidate c.optimal
  valid := valid_of_state _ ((interpret c.state).selectedInstall (selectedProvider H)) rfl rfl
    c.candidate_eq (by simp [Data.install, interpret, State.selectedInstall]) c.optimal_eq

theorem interpret_install (c : Cache H) :
    interpret c.install = (interpret c.state).selectedInstall (selectedProvider H) := by
  apply state_ext
  · rfl
  · rfl
  · exact c.candidate_eq
  · simp [interpret, install, Data.install, State.selectedInstall]

end Cache

/-- One call returns one whole row. Implementations must retain the solved
closure before decoding coordinates. The cost of a call remains explicit. -/
structure Optimizer (H : ∃ P, selector P) where
  solve : (s : Code G D L) → (p : Pair n) → p ∈ (interpret s).remaining → Row n
  solve_eq : ∀ (s : Code G D L) (p : Pair n) (hp : p ∈ (interpret s).remaining) (v : Fin n),
    (((solve s p hp)[v.val] : ℕ) : ℝ≥0) / L = (selectedProvider H).family (interpret s) p v
  inactive_eq : ∀ s p, p ∉ (interpret s).remaining → (selectedProvider H).family (interpret s) p = 0

/-- Strict array materialization invokes `solve` once per active pair. Each
returned row is retained before any mass scan reads its coordinates. -/
def buildFamily {H : ∃ P, selector P} (Q : Optimizer H)
    (s : Code G D L) : Family n :=
  Vector.ofFn fun u => Vector.ofFn fun v =>
    if hp : flag s.data.remaining (u, v) = true then
      Q.solve s (u, v) ((mem_remainingSet _ _).mpr hp)
    else Vector.replicate n 0

theorem buildFamily_eq {H : ∃ P, selector P} (Q : Optimizer H)
    (s : Code G D L) : weights L (buildFamily Q s) = (selectedProvider H).family (interpret s) := by
  funext p v
  dsimp only [weights, row, buildFamily]
  simp only [Vector.getElem_ofFn]
  by_cases hp : flag s.data.remaining p = true
  · simp only [dite_eq_left hp]
    exact Q.solve_eq s p ((mem_remainingSet _ _).mpr hp) v
  · simp only [dite_eq_right hp, Vector.getElem_replicate, Nat.cast_zero, zero_div]
    simpa using (congrFun (Q.inactive_eq s p
      (fun h => hp ((mem_remainingSet _ _).mp h))) v).symm

/-- The whole family is built once, then its stored coordinates are summed once. -/
def refresh {H : ∃ P, selector P} (Q : Optimizer H)
    (s : Code G D L) : Cache H :=
  let w := buildFamily Q s
  { state := s, candidate := w,
    optimal := massNumerator s.data.remaining s.data.cut w,
    candidate_eq := buildFamily_eq Q s, optimal_eq := rfl }

noncomputable def midpointLevel (hL : 0 < L) (j : Fin L) : AdaptiveEpoch.UnitLevel :=
  ⟨(GridLevelSampling.midpoint L j).toNNReal, by
    exact Real.toNNReal_le_one.mpr
      (GridLevelSampling.cell_subset_unit hL j (GridLevelSampling.midpoint_mem_cell hL j)).2⟩

/-- The only distance-dependent interface. Equality is of the complete cut,
including source/target conventions and unreachable vertices. -/
structure CutOracle (G : Digraph (Fin n)) (L : ℕ) (hL : 0 < L) where
  cut : Row n → Fin n → Fin L → Flags n
  cut_eq : ∀ a s j,
    cutSet (cut a s j) = levelCut G (fun v => (a[v.val] : ℝ≥0) / L) s
      (midpointLevel hL j).val

def sampleRound (hL : 0 < L) (C : CutOracle G L hL) (s : Code G D L)
    (p : Pair n) (hp : p ∈ (interpret s).remaining) (j : Fin L) : Code G D L where
  data := s.data.round p (C.cut (row s.data.weights p) p.1 j)
  valid := valid_of_state _
    ((interpret s).round p hp (midpointLevel hL j).val (midpointLevel hL j).property)
    (by simp [Data.round, interpret, State.round])
    (by
      simp only [Data.round, interpret, State.round, cutSet_unionFlags, C.cut_eq]
      rfl)
    rfl rfl rfl

theorem interpret_sampleRound (hL : 0 < L) (C : CutOracle G L hL)
    (s : Code G D L) (p : Pair n) (hp : p ∈ (interpret s).remaining) (j : Fin L) :
    interpret (sampleRound hL C s p hp j) =
      (interpret s).round p hp (midpointLevel hL j).val (midpointLevel hL j).property := by
  apply state_ext
  · simp [interpret, sampleRound, Data.round, State.round]
  · simp only [interpret, sampleRound, Data.round, State.round, cutSet_unionFlags, C.cut_eq]
    rfl
  · rfl
  · rfl

section ClosureAdapter
open CandidateClosureProvider CandidateGridOptimizer CandidateThresholdClosure
open CandidatePortDifferenceSystem CandidateGridRounding
variable [DecidableRel G.Adj]

/-- A concrete materialization boundary for the existing closure recursion.
The final closure is bound before constructing the coordinate array, so the
solver call is outside the coordinate callback. The separate tabulated-flow
implementation may replace this body under the same exact-vector contract. -/
noncomputable def closureRow (hL : 0 < L)
    (E : ResidualSearch.Enumeration (MinimumClosureCut.Vertex (Node (Point (Fin n)) L)))
    (s : Code G D L) (p : Pair n) (hp : p ∈ (interpret s).remaining) : Row n :=
  let S := system G p.1 p.2 (cutSet s.data.cut) L (4 * s.data.scale)
  let c := integerCosts (cutSet s.data.cut)
  let H := finiteHooks (candidateClosure G p.1 p.2 (cutSet s.data.cut) L (4 * s.data.scale)) E
  let hf := system_nonempty G p.1 p.2 (cutSet s.data.cut) L (4 * s.data.scale) hL
    (FlexibleClosureRounding.current_feasible (interpret s) s.data.scale rfl p hp)
  let T := closureSet (problem S c) H
  let q := decode S c T (closureSet_optimal (problem S c) H (closure_nonempty S c hf)).1
  Vector.ofFn fun v => if v ∈ cutSet s.data.cut then L else
    (((q (TerminalPorts.core v, true) : ℕ) : ℤ) -
      (q (TerminalPorts.core v, false) : ℕ)).toNat

theorem closureRow_eq_numerator (hL : 0 < L)
    (E : ResidualSearch.Enumeration (MinimumClosureCut.Vertex (Node (Point (Fin n)) L)))
    (s : Code G D L) (p : Pair n) (hp : p ∈ (interpret s).remaining) (v : Fin n) :
    (closureRow hL E s p hp)[v.val] =
      (candidateNumerator G p.1 p.2 (cutSet s.data.cut) L (4 * s.data.scale) hL
        (finiteHooks (candidateClosure G p.1 p.2 (cutSet s.data.cut) L (4 * s.data.scale)) E)
        (FlexibleClosureRounding.current_feasible (interpret s) s.data.scale rfl p hp) v).toNat := by
  simp only [closureRow, Vector.getElem_ofFn, candidateNumerator, candidateGrid, gridPoint]
  split_ifs <;> simp

/-- This adapter certifies equality to the closure-selected flexible law's
actual family, including its zero rows on inactive labels. -/
noncomputable def closureOptimizer (hL : 0 < L)
    (E : ResidualSearch.Enumeration (MinimumClosureCut.Vertex (Node (Point (Fin n)) L))) :
    Optimizer (providerWitness (provider (FlexibleClosureRounding.closureGridOptimizer hL E) :
      FamilyProvider G D (L : ℝ≥0))) where
  solve := closureRow hL E
  solve_eq := by
    intro s p hp v
    simp only [selectedProvider_eq]
    rw [selected_eq_of_scale _ (interpret s) s.data.scale rfl]
    change ((closureRow hL E s p hp)[v.val] : ℝ≥0) / L =
      familyWeights G (interpret s).remaining (interpret s).cut L (4 * s.data.scale) hL
        (finiteFamilyHooks G (interpret s).cut L (4 * s.data.scale) E)
        (FlexibleClosureRounding.current_feasible (interpret s) s.data.scale rfl) p v
    simp only [familyWeights, dite_eq_left hp]
    apply NNReal.coe_injective
    rw [candidateWeights_numerator]
    simp only [NNReal.coe_div, NNReal.coe_natCast, closureRow_eq_numerator]
    congr 1
    exact_mod_cast Int.toNat_of_nonneg
      (candidateNumerator_nonneg G p.1 p.2 (interpret s).cut L (4 * s.data.scale) hL
        (finiteFamilyHooks G (interpret s).cut L (4 * s.data.scale) E p)
        (FlexibleClosureRounding.current_feasible (interpret s) s.data.scale rfl p hp) v)
  inactive_eq := by
    intro s p hp
    simp only [selectedProvider_eq]
    rw [selected_eq_of_scale _ (interpret s) s.data.scale rfl]
    change familyWeights G (interpret s).remaining (interpret s).cut L (4 * s.data.scale) hL
      (finiteFamilyHooks G (interpret s).cut L (4 * s.data.scale) E)
      (FlexibleClosureRounding.current_feasible (interpret s) s.data.scale rfl) p = 0
    simp only [familyWeights, dite_eq_right hp]
    rfl

end ClosureAdapter

/-- A supplied finite demand mask is checked against the mathematical
threshold demands. Computing that mask is a separate shortest-path task. -/
def initialCode (G : Digraph (Fin n)) (hL : 1 ≤ (L : ℝ≥0))
    (a : PairFlags n) (ha : remainingSet a = CandidateSchedule.unweightedDemands G (L : ℝ≥0)) :
    Code G (CandidateSchedule.unweightedDemands G (L : ℝ≥0)) L := by
  let x : Flags n := Vector.replicate n false
  let w : Family n := Vector.replicate n (Vector.replicate n (Vector.replicate n 1))
  let s : Data n := ⟨a, x, w, 1, massNumerator a x w⟩
  refine ⟨s, valid_of_state s (CandidateSchedule.initial G (L : ℝ≥0) hL) ha ?_ ?_ ?_ rfl⟩
  · ext v
    simp [s, x, CandidateSchedule.initial]
  · funext p v
    simp [s, w, weights, row, CandidateSchedule.initial]
  · simp [s, CandidateSchedule.initial]

theorem interpret_initialCode (G : Digraph (Fin n)) (hL : 1 ≤ (L : ℝ≥0))
    (a : PairFlags n) (ha : remainingSet a = CandidateSchedule.unweightedDemands G (L : ℝ≥0)) :
    interpret (initialCode G hL a ha) = CandidateSchedule.initial G (L : ℝ≥0) hL := by
  apply state_ext
  · exact ha
  · ext v
    simp [interpret, initialCode, CandidateSchedule.initial]
  · funext p v
    simp [interpret, initialCode, weights, row, CandidateSchedule.initial]
  · simp [interpret, initialCode, CandidateSchedule.initial]

/-- Executable entry using the supplied demand mask as its type index. This
avoids passing the classical real-distance demand set as a runtime argument;
`ha` still certifies exact equality to that set. -/
def initialMaskedCode (G : Digraph (Fin n)) (hL : 1 ≤ (L : ℝ≥0))
    (a : PairFlags n) (ha : remainingSet a = CandidateSchedule.unweightedDemands G (L : ℝ≥0)) :
    Code G (remainingSet a) L where
  data := (initialCode G hL a ha).data
  valid :=
    { remaining_subset := Finset.Subset.refl _
      feasible := (initialCode G hL a ha).valid.feasible
      cap := (initialCode G hL a ha).valid.cap
      processed := fun _ hp hnot => (hnot hp).elim
      current_eq := (initialCode G hL a ha).valid.current_eq }

/-- A direct size bound for stored numerator masses. This statement counts
values, not the running time of producing them. -/
theorem massNumerator_le (a : PairFlags n) (x : Flags n) (w : Family n)
    (hw : ∀ (p : Pair n) (v : Fin n), (row w p)[v.val] ≤ L) :
    massNumerator a x w ≤ n * n * n * L := by
  have ha : (remainingSet a).card ≤ n * n := by
    simpa [Fintype.card_prod] using (remainingSet a).card_le_univ
  have hx : (Finset.univ.filter (fun v : Fin n => x[v.val] = false)).card ≤ n := by
    simpa using (Finset.univ.filter (fun v : Fin n => x[v.val] = false)).card_le_univ
  calc
    massNumerator a x w ≤ ∑ p ∈ remainingSet a,
        ∑ v ∈ Finset.univ.filter (fun v : Fin n => x[v.val] = false), L := by
      exact Finset.sum_le_sum fun p _ => Finset.sum_le_sum fun v _ => hw p v
    _ = (remainingSet a).card *
        (Finset.univ.filter (fun v : Fin n => x[v.val] = false)).card * L := by
      simp [mul_assoc]
    _ ≤ n * n * n * L := Nat.mul_le_mul_right L (Nat.mul_le_mul ha hx)

theorem closureRow_le [DecidableRel G.Adj] (hL : 0 < L)
    (E : ResidualSearch.Enumeration
      (MinimumClosureCut.Vertex (CandidateThresholdClosure.Node (CandidateGridOptimizer.Point (Fin n)) L)))
    (s : Code G D L) (p : Pair n) (hp : p ∈ (interpret s).remaining) (v : Fin n) :
    (closureRow hL E s p hp)[v.val] ≤ L := by
  rw [closureRow_eq_numerator, Int.toNat_le]
  exact CandidateClosureProvider.candidateNumerator_le G p.1 p.2 (cutSet s.data.cut)
    L (4 * s.data.scale) hL _ _ v

section ExecutableAdapters
open CandidateGridOptimizer CandidateThresholdClosure
variable [DecidableRel G.Adj]

omit [DecidableRel G.Adj] in
theorem current_feasible_data (s : Code G D L) (p : Pair n)
    (hp : p ∈ (interpret s).remaining) :
    CandidateClosureProvider.CandidateFeasible G p.1 p.2 (cutSet s.data.cut)
      L (4 * s.data.scale) :=
  FlexibleClosureRounding.current_feasible (interpret s) s.data.scale rfl p hp

/-- The executable tabulated closure is computed once. Conversion to an array
only reads the retained integer table and never calls the optimizer again. -/
def tabulatedRow (hL : 0 < L) (EV : ResidualSearch.Enumeration (Fin n))
    (E : ResidualSearch.Enumeration (MinimumClosureCut.Vertex (Node (Point (Fin n)) L)))
    (s : Code G D L) (p : Pair n) (hp : p ∈ (interpret s).remaining) : Row n :=
  let values := ClosureRuntime.candidateNumerators G p.1 p.2 (cutSet s.data.cut)
    L (4 * s.data.scale) hL EV E
    (current_feasible_data s p hp)
  Vector.ofFn fun v => (IntegralNetworkFlow.Tabulated.read v values).1.toNat

theorem tabulatedRow_eq (hL : 0 < L) (EV : ResidualSearch.Enumeration (Fin n))
    (E : ResidualSearch.Enumeration (MinimumClosureCut.Vertex (Node (Point (Fin n)) L)))
    (s : Code G D L) (p : Pair n) (hp : p ∈ (interpret s).remaining) :
    tabulatedRow hL EV E s p hp = closureRow hL E s p hp := by
  apply Vector.ext
  intro i hi
  simp only [tabulatedRow, Vector.getElem_ofFn]
  rw [ClosureRuntime.candidateNumerators_read]
  exact (closureRow_eq_numerator hL E s p hp ⟨i, hi⟩).symm

/-- A concrete executable optimizer satisfies the exact selected-family
adapter, with one retained closure result for each solved label. -/
def tabulatedOptimizer (hL : 0 < L) (EV : ResidualSearch.Enumeration (Fin n))
    (E : ResidualSearch.Enumeration (MinimumClosureCut.Vertex (Node (Point (Fin n)) L))) :
    Optimizer (providerWitness (provider (FlexibleClosureRounding.closureGridOptimizer hL E) :
      FamilyProvider G D (L : ℝ≥0))) where
  solve := tabulatedRow hL EV E
  solve_eq := by
    intro s p hp v
    rw [tabulatedRow_eq]
    exact (closureOptimizer hL E).solve_eq s p hp v
  inactive_eq := (closureOptimizer hL E).inactive_eq

/-- A concrete shortest-path cut is retained before the Boolean flag array
is materialized. The cut's own primitive count is exposed by IntegerLevelCuts. -/
def integerCutOracle (hL : 0 < L) (EV : ResidualSearch.Enumeration (Fin n)) :
    CutOracle G L hL where
  cut := fun a s j =>
    let y := IntegerLevelCuts.cut EV G (fun v => a[v.val]) s j.val
    Vector.ofFn fun v => decide (v ∈ y.1)
  cut_eq := by
    intro a s j
    have hflags : cutSet (Vector.ofFn fun v : Fin n =>
        decide (v ∈ (IntegerLevelCuts.cut EV G (fun v => a[v.val]) s j.val).1)) =
        (IntegerLevelCuts.cut EV G (fun v => a[v.val]) s j.val).1 := by
      ext v
      simp
    exact hflags.trans (IntegerLevelCuts.cut_correct EV G (fun v => a[v.val]) hL s j)

end ExecutableAdapters

end
end DirectedFlowCutGap.RetainedGridState
