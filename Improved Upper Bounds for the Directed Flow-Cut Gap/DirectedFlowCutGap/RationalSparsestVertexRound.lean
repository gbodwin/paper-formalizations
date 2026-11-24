import DirectedFlowCutGap.RationalSparsestVertexThreshold
import DirectedFlowCutGap.RationalSparsestEdgeRound

/-! Round a computed positive vertex threshold on the literal tape.
Lengths alone are scaled, and a demand's endpoints are excluded. -/
namespace DirectedFlowCutGap.RationalSparsestVertexRound

open scoped BigOperators NNReal NNRat ENNReal
open BinaryArithmetic (Bits)
open BinaryFractionalWalkOracle (Adjacency graph)
open BinaryFractionalRows (Row)
open RationalSparsestVertexDistances (weights)
open RationalSparsestVertexThreshold (choose actualDistance)
open RationalSparsestEdgeRound (demandSet)
open EncodedUnitCostReplication (Input selectedSet)
open RawNonnegativeRational (Code)
open RetainedGridState (Flags)
open FiniteDrawTrees (ideal)

variable {m n : ℕ}

def scaled (A : Adjacency n) (w c : Row n) (τ : ℚ≥0) : Input n :=
  let t := Code.ofNNRat τ
  ⟨A, w.map (fun q => (BinaryRational.decode q).div t), c.map BinaryRational.decode⟩

theorem scaled_graph (A : Adjacency n) (w c : Row n) (τ : ℚ≥0) :
    (scaled A w c τ).graph = graph A := rfl

theorem scaled_weight (A : Adjacency n) (w c : Row n) (τ : ℚ≥0) :
    (scaled A w c τ).weight = fun j => weights w j / (τ : ℝ≥0) := by
  funext j
  simp only [scaled, Input.weight, Vector.getElem_map, weights, Code.realValue, Code.value_div,
    Code.value_ofNNRat, NNRat.cast_div]

theorem scaled_price (A : Adjacency n) (w c : Row n) (τ : ℚ≥0) :
    (scaled A w c τ).cost = weights c := by
  funext j
  simp only [scaled, Input.cost, Vector.getElem_map, weights, Code.realValue]

def tree (D : Input n) (mode : ChargedVertexModes.Mode) : FiniteDrawTrees.Tree (Flags n) :=
  ChargedVertexModes.round n mode D

def round (D : Input n) (mode : ChargedVertexModes.Mode) (T : ℕ) (tape : Bits) :
    Option (Flags n × Bits) :=
  (PaidVertexRounding.runner mode T D tape).1.map PhysicalIntegerRounding.Result.observe

theorem round_reference (D : Input n) (mode : ChargedVertexModes.Mode) (T : ℕ) (tape : Bits) :
    round D mode T tape = LiteralTapeComposition.execute T (tree D mode) tape := by
  rw [round, PaidVertexRounding.runner_value]
  exact PhysicalAmplifiedBinaryVertex.runner_observe mode T D tape

theorem round_valid (D : Input n) (mode : ChargedVertexModes.Mode) (T : ℕ)
    {tape rest : Bits} {mask : Flags n} (ran : round D mode T tape = some (mask,rest)) :
    IsIntegralCut D.graph (selectedSet mask) (thresholdDemands D.graph D.weight) := by
  rw [round_reference, LiteralTapeComposition.execute] at ran
  obtain ⟨⟨output,receipt⟩, read, same⟩ := Option.map_eq_some_iff.mp ran
  have sameMask : output = mask := congrArg Prod.fst same
  subst output
  have support := EncodedSolverBits.run_support (LazyFairBitTrees.lower_binary T (tree D mode)) read
  cases mode
  · exact EncodedWeightedRounding.bit_support_valid T D support
  · exact EncodedSizeRounding.bit_support_valid T D support

def drawBound (n : ℕ) : ℕ := EncodedUniformRounding.drawBound (4*n^2)
def tapeBudget (n T : ℕ) : ℕ := drawBound n*T*EncodedWeightedRounding.drawWidth n

private theorem tree_bounds (D : Input n) (mode : ChargedVertexModes.Mode) :
    FiniteDrawTrees.Within (drawBound n) (tree D mode) ∧
      LazyFairBitTrees.WidthsLE (EncodedWeightedRounding.drawWidth n) (tree D mode) := by
  cases mode
  · exact ⟨EncodedWeightedRounding.tree_within D, EncodedWeightedRounding.tree_widths D⟩
  · exact ⟨EncodedSizeRounding.tree_within D, EncodedSizeRounding.tree_widths D⟩

theorem round_fairTape (D : Input n) (mode : ChargedVertexModes.Mode) (T : ℕ) :
    (EncodedSolverBits.fairTape (tapeBudget n T)).map (fun bits => (round D mode T bits).map Prod.fst) =
      (ideal (LazyFairBitTrees.lower T (tree D mode))).map some := by
  obtain ⟨draws,width⟩ := tree_bounds D mode
  have binary := LazyFairBitTrees.lower_binary T (tree D mode)
  have budget : FiniteDrawTrees.Within (tapeBudget n T) (LazyFairBitTrees.lower T (tree D mode)) :=
    LazyFairBitTrees.lower_within draws width T
  simp only [round_reference, LiteralTapeComposition.execute, Option.map_map, Function.comp_def]
  exact EncodedSolverBits.run_fairTape budget binary

theorem round_complete (D : Input n) (mode : ChargedVertexModes.Mode) (T : ℕ) (tape : Bits)
    (enough : tapeBudget n T ≤ tape.length) :
    ∃ mask used, round D mode T tape = some (mask,tape.drop used) ∧ used ≤ tapeBudget n T := by
  obtain ⟨draws,width⟩ := tree_bounds D mode
  have binary := LazyFairBitTrees.lower_binary T (tree D mode)
  have budget : FiniteDrawTrees.Within (tapeBudget n T) (LazyFairBitTrees.lower T (tree D mode)) :=
    LazyFairBitTrees.lower_within draws width T
  obtain ⟨mask,used,read,within⟩ := EncodedSolverBits.complete budget binary tape enough
  exact ⟨mask,used,by rw [round_reference, LiteralTapeComposition.execute, read]; rfl,within⟩

inductive Result (n : ℕ) where
  | zeroDistance
  | cut (mask : Flags n) (suffix : Bits)

def run (A : Adjacency n) (w c : Row n) (P : Vector (Fin n × Fin n) m)
    (mode : ChargedVertexModes.Mode) (T : ℕ) (tape : Bits) : Option (Result n) :=
  match choose A w P with
  | .unreachable _ => some (.cut (Vector.replicate n false) tape)
  | .zero => some .zeroDistance
  | .threshold _ τ => (round (scaled A w c τ) mode T tape).map (fun (mask,rest) => .cut mask rest)

theorem run_complete (A : Adjacency n) (w c : Row n) (P : Vector (Fin n × Fin n) m)
    {i : Fin m} {τ : ℚ≥0} (chosen : choose A w P = .threshold i τ)
    (mode : ChargedVertexModes.Mode) (T : ℕ) (tape : Bits)
    (enough : tapeBudget n T ≤ tape.length) :
    ∃ mask used, run A w c P mode T tape = some (.cut mask (tape.drop used)) ∧
      used ≤ tapeBudget n T := by
  obtain ⟨mask,used,read,paid⟩ := round_complete (scaled A w c τ) mode T tape enough
  exact ⟨mask,used,by simp only [run, chosen, read, Option.map_some],paid⟩

theorem threshold_demand (A : Adjacency n) (w c : Row n) (P : Vector (Fin n × Fin n) m)
    {i : Fin m} {τ : ℚ≥0} (found : choose A w P = .threshold i τ) (j : Fin m) :
    P[j.val] ∈ thresholdDemands (scaled A w c τ).graph (scaled A w c τ).weight ↔
      (τ : ℝ≥0) ≤ actualDistance A w P j := by
  have spec := RationalSparsestVertexThreshold.choose_spec A w P
  rw [found] at spec
  obtain ⟨finite,_,positive,_,_⟩ := spec
  have pos : (0 : ℝ≥0) < (τ : ℝ≥0) := by exact_mod_cast positive
  rw [scaled_graph, scaled_weight, SparsestVertexBridge.mem_scaled_threshold _ _ _ pos]
  have read : ((actualDistance A w P j : ℝ≥0) : ℝ≥0∞) =
      vertexDistance (graph A) (weights w) P[j.val].1 P[j.val].2 :=
    ENNReal.coe_toNNReal (finite j)
  rw [← read, ENNReal.coe_le_coe]

private theorem demanded (P : Vector (Fin n × Fin n) m) (i : Fin m) :
    P[i.val] ∈ demandSet P := Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩

private theorem separated (A : Adjacency n) (w c : Row n) (P : Vector (Fin n × Fin n) m)
    {i : Fin m} {τ : ℚ≥0} {X : Finset (Fin n)}
    (chosen : choose A w P = .threshold i τ)
    (valid : IsIntegralCut (scaled A w c τ).graph X
      (thresholdDemands (scaled A w c τ).graph (scaled A w c τ).weight))
    (j : Fin m) (above : (τ : ℝ≥0) ≤ actualDistance A w P j) :
    (⟨P[j.val], demanded P j⟩ : demandSet P) ∈ SparsestVertexBridge.separated (graph A) (demandSet P) X := by
  classical
  refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
  exact valid P[j.val].1 P[j.val].2 ((threshold_demand A w c P chosen j).mpr above)

theorem count_le (A : Adjacency n) (w c : Row n) (P : Vector (Fin n × Fin n) m)
    (distinct : Function.Injective fun i : Fin m => P[i.val])
    {i : Fin m} {τ : ℚ≥0} {X : Finset (Fin n)}
    (chosen : choose A w P = .threshold i τ)
    (valid : IsIntegralCut (scaled A w c τ).graph X
      (thresholdDemands (scaled A w c τ).graph (scaled A w c τ).weight)) :
    (FiniteHarmonicThreshold.above (actualDistance A w P) (τ : ℝ≥0)).card ≤
      (SparsestVertexBridge.separated (graph A) (demandSet P) X).card := by
  let includePair (j : Fin m) : demandSet P := ⟨P[j.val], demanded P j⟩
  have injection : Function.Injective includePair := fun _ _ same => distinct (congrArg Subtype.val same)
  apply Finset.card_le_card_of_injOn includePair _ injection.injOn
  intro j inside
  exact separated A w c P chosen valid j (Finset.mem_filter.mp inside).2

theorem run_cut (A : Adjacency n) (w c : Row n) (P : Vector (Fin n × Fin n) m)
    (mode : ChargedVertexModes.Mode) (T : ℕ) {tape rest : Bits} {mask : Flags n}
    (ran : run A w c P mode T tape = some (.cut mask rest)) :
    0 < (SparsestVertexBridge.separated (graph A) (demandSet P) (selectedSet mask)).card := by
  have spec := RationalSparsestVertexThreshold.choose_spec A w P
  cases found : choose A w P with
  | unreachable i =>
    rw [found] at spec
    simp only [run, found, Option.some.injEq, Result.cut.injEq] at ran
    obtain ⟨rfl,rfl⟩ := ran
    have empty : selectedSet (Vector.replicate n false) = ∅ := by
      ext j
      simp [selectedSet]
    rw [empty]
    exact (SparsestVertexBridge.unreachable_zero_sparsity (graph A) (weights c) (weights w)
      (demandSet P) P[i.val] (demanded P i) spec).1
  | zero =>
    simp only [run, found, Option.some.injEq] at ran
    cases ran
  | threshold i τ =>
    rw [found] at spec
    rw [run, found] at ran
    obtain ⟨⟨output,tail⟩, performed, equal⟩ := Option.map_eq_some_iff.mp ran
    obtain ⟨rfl,rfl⟩ := Result.cut.inj equal
    have valid := round_valid (scaled A w c τ) mode T performed
    exact Finset.card_pos.mpr ⟨_, separated A w c P found valid i (le_of_eq spec.2.1.symm)⟩

end DirectedFlowCutGap.RationalSparsestVertexRound
