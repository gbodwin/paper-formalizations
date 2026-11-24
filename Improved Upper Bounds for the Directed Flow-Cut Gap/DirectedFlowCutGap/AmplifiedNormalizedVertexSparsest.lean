import DirectedFlowCutGap.AmplifiedSparsestVertexTape
import DirectedFlowCutGap.NormalizedVertexLPRound

/-! Compute the exact normalized vertex lengths once, then amplify the
selected sparsity scale on a bounded fair-bit tape. -/
namespace DirectedFlowCutGap.AmplifiedNormalizedVertexSparsest

open scoped BigOperators NNReal NNRat
open BinaryArithmetic (Bits)
open BinaryFractionalWalkOracle (Adjacency graph)
open BinaryFractionalRows (Row)
open RetainedGridState (Flags)
open EncodedUnitCostReplication (selectedSet)
open RationalSparsestVertexDistances (weights)
open RationalSparsestVertexThreshold (choose actualDistance)
open RationalSparsestVertexRound (scaled tree)
open RationalSparsestVertexExpectation (expectedSparsity normalizedMass)
open RationalSparsestEdgeRound (demandSet)
open NormalizedVertexLPRound (pick solution)
open ConcurrentEdgeBudgetSelection (scale)
open AmplifiedSparsestVertexTape (budget round supported cut_support)

attribute [local instance] EncodedUniformRounding.flagsFintype

variable {m n : ℕ}

def run (A : Adjacency n) (c : Row n) (P : Vector (Fin n × Fin n) m)
    (extra confidence : ℕ) (bits : Bits) : Option (ℚ × Flags n × Bits) :=
  (NormalizedVertexLP.minimize A c P.get m).bind fun (q,w) =>
    match choose A w P with
    | .threshold _ τ => (round A c P (scaled A w c τ) (pick A w q P) extra confidence bits).map
      fun sample => (q,sample)
    | _ => none

theorem complete (A : Adjacency n) (c : Row n) (P : Vector (Fin n × Fin n) m)
    (reach : ∀ j : Fin m, Nonempty (SimplePath (graph A) (P.get j).1 (P.get j).2))
    (d : Fin m) (different : (P.get d).1 ≠ (P.get d).2) (noArc : ¬ (graph A).Adj (P.get d).1 (P.get d).2)
    (extra confidence : ℕ) (bits : Bits) (enough : budget n extra confidence ≤ bits.length) :
    ∃ q mask used, run A c P extra confidence bits = some (q,mask,bits.drop used) ∧
      used ≤ budget n extra confidence := by
  obtain ⟨q,w,i,τ,solved,threshold⟩ := solution A c P reach d different noArc
  obtain ⟨mask,used,ran,paid⟩ := AmplifiedSparsestVertexTape.complete A c P (scaled A w c τ)
    (pick A w q P) extra confidence bits enough
  exact ⟨q,mask,used,by simp only [run,solved,Option.bind_some,threshold,ran,Option.map_some],paid⟩

private theorem read_round (A : Adjacency n) (c : Row n) (P : Vector (Fin n × Fin n) m)
    (extra confidence : ℕ) {bits rest : Bits} {price : ℚ} {mask : Flags n}
    (ran : run A c P extra confidence bits = some (price,mask,rest)) :
    ∃ w i τ, NormalizedVertexLP.minimize A c P.get m = some (price,w) ∧ choose A w P = .threshold i τ ∧
      round A c P (scaled A w c τ) (pick A w price P) extra confidence bits = some (mask,rest) := by
  obtain ⟨⟨q,w⟩,found,after⟩ := Option.bind_eq_some_iff.mp ran
  cases threshold : choose A w P with
  | unreachable => simp [threshold] at after
  | zero => simp [threshold] at after
  | threshold i τ =>
    simp only [threshold] at after
    obtain ⟨pair,read,same⟩ := Option.map_eq_some_iff.mp after
    obtain ⟨rfl,rfl⟩ := Prod.mk.inj same
    exact ⟨w,i,τ,found,threshold,read⟩

private theorem separated_count (A : Adjacency n) (w c : Row n) (P : Vector (Fin n × Fin n) m)
    (distinct : Function.Injective fun j : Fin m => P[j.val]) {i : Fin m} {τ : ℚ≥0}
    (threshold : choose A w P = .threshold i τ) {mode : ChargedVertexModes.Mode} {mask : Flags n}
    (seen : mask ∈ (FiniteDrawTrees.ideal (tree (scaled A w c τ) mode)).support) :
    0 < (SparsestVertexBridge.separated (graph A) (demandSet P) (selectedSet mask)).card := by
  have valid := cut_support (scaled A w c τ) mode seen
  have spec := RationalSparsestVertexThreshold.choose_spec A w P
  rw [threshold] at spec
  exact spec.2.2.2.1.trans_le (RationalSparsestVertexRound.count_le A w c P distinct threshold valid)

theorem cut_valid (A : Adjacency n) (c : Row n) (P : Vector (Fin n × Fin n) m)
    (distinct : Function.Injective fun j : Fin m => P[j.val]) (extra confidence : ℕ)
    {bits rest : Bits} {price : ℚ} {mask : Flags n}
    (ran : run A c P extra confidence bits = some (price,mask,rest)) :
    0 < (SparsestVertexBridge.separated (graph A) (demandSet P) (selectedSet mask)).card := by
  obtain ⟨w,i,τ,_,threshold,read⟩ := read_round A c P extra confidence ran
  exact separated_count A w c P distinct threshold
    (supported A c P (scaled A w c τ) (pick A w price P) extra confidence read)

private theorem normal_read (A : Adjacency n) (w c : Row n) (P : Vector (Fin n × Fin n) m)
    (reach : ∀ j : Fin m, Nonempty (SimplePath (graph A) (P.get j).1 (P.get j).2))
    {q : ℚ} (solved : NormalizedVertexLP.minimize A c P.get m = some (q,w)) :
    (m : ℝ≥0) ≤ ∑ j, actualDistance A w P j := by
  have norm := (NormalizedVertexLP.minimize_attained A c P.get (m : ℚ≥0) reach solved).1
  have entry (i : Fin m) : P.get i = P[i.val] := by cases i; rfl
  simpa only [actualDistance,entry,NNRat.cast_natCast] using norm

noncomputable section
open FiniteDrawTrees (ideal)
open FiniteAmplification (probability)

theorem zero_cut (A : Adjacency n) (c : Row n) (P : Vector (Fin n × Fin n) m)
    (distinct : Function.Injective fun j : Fin m => P[j.val])
    (reach : ∀ j : Fin m, Nonempty (SimplePath (graph A) (P.get j).1 (P.get j).2))
    (extra confidence : ℕ) {bits rest : Bits} {mask : Flags n}
    (ran : run A c P extra confidence bits = some (0,mask,rest)) :
    cutCost (weights c) (selectedSet mask) = 0 := by
  obtain ⟨w,i,τ,solved,threshold,read⟩ := read_round A c P extra confidence ran
  let D := scaled A w c τ
  let mode := pick A w 0 P
  let p := ideal (tree D mode)
  let cost (x : Flags n) : ℝ := SparsestVertexBridge.sparsity (graph A) (weights c) (demandSet P) (selectedSet x)
  have free : weightedCost (weights c) (weights w) = 0 := by
    have price := (NormalizedVertexLP.minimize_attained A c P.get (m : ℚ≥0) reach solved).2.1
    exact NNReal.coe_eq_zero.mp (by simpa only [Rat.cast_zero] using price)
  obtain ⟨K,_,bound⟩ := NormalizedVertexLPRound.ideal_bound 1 zero_lt_one
  have expected : FiniteAmplification.expectedCost p cost ≤ 0 := by
    have h := bound A w c P distinct (normal_read A w c P reach solved) threshold mode
    change FiniteAmplification.expectedCost (ideal (tree D mode))
      (fun x => (SparsestVertexBridge.sparsity (graph A) (weights c) (demandSet P) (selectedSet x) : ℝ)) ≤ 0
    simpa only [RationalSparsestVertexExpectation.expectedSparsity,RationalSparsestVertexRound.scaled_graph,
      RationalSparsestVertexRound.scaled_price,free,scale,NNReal.coe_zero,zero_div,zero_mul,mul_zero] using h
  have seen : mask ∈ p.support := supported A c P D mode extra confidence read
  have zero := FiniteAmplification.cost_eq_zero_on_support p cost (fun _ => NNReal.coe_nonneg _) expected seen
  have count := separated_count A w c P distinct threshold seen
  have countPositive :
      (0 : ℝ≥0) < ((SparsestVertexBridge.separated (graph A) (demandSet P) (selectedSet mask)).card : ℝ≥0) := by
    exact_mod_cast count
  have div : cutCost (weights c) (selectedSet mask) /
      ((SparsestVertexBridge.separated (graph A) (demandSet P) (selectedSet mask)).card : ℝ≥0) = 0 :=
    NNReal.coe_eq_zero.mp zero
  exact (div_eq_zero_iff.mp div).resolve_right countPositive.ne'

theorem failure : ∀ ε : ℝ, 0 < ε → ∃ K : ℝ, 0 < K ∧ ∀ {m n : ℕ}
    (A : Adjacency n) (c : Row n) (P : Vector (Fin n × Fin n) m)
    (_distinct : Function.Injective fun j : Fin m => P[j.val])
    (_reach : ∀ j : Fin m, Nonempty (SimplePath (graph A) (P.get j).1 (P.get j).2))
    {q : ℚ} {w : Row n}, NormalizedVertexLP.minimize A c P.get m = some (q,w) →
    ∀ {i : Fin m} {τ : ℚ≥0}, choose A w P = .threshold i τ →
    ∀ mode : ChargedVertexModes.Mode, ∀ extra confidence : ℕ,
      let B := K*(n : ℝ)^ε*scale n m (weightedCost (weights c) (weights w)) (normalizedMass A w P) mode
      0 < B →
      probability ((EncodedSolverBits.fairTape (budget n extra confidence)).map
        (fun bits => (run A c P extra confidence bits).map fun (_,mask,_) => mask))
        (RationalSparsestVertexFairTape.bad (scaled A w c τ) (demandSet P) (2*B)) ≤
          ((1 : ℝ)/2)^(extra+1)+((1 : ℝ)/2)^confidence := by
  intro ε epos
  obtain ⟨K,Kpos,bound⟩ := NormalizedVertexLPRound.ideal_bound ε epos
  refine ⟨K,Kpos,?_⟩
  intro m n A c P distinct reach q w found i τ threshold mode extra confidence B Bpositive
  let D := scaled A w c τ
  let chosenMode := pick A w q P
  have price := (NormalizedVertexLP.minimize_attained A c P.get (m : ℚ≥0) reach found).2.1
  have expected : expectedSparsity D (demandSet P) chosenMode ≤ B :=
    (bound A w c P distinct (normal_read A w c P reach found) threshold chosenMode).trans
      (mul_le_mul_of_nonneg_left (NormalizedVertexLPRound.picked_le A w c P q price mode) (by positivity))
  have observed :
      (fun bits : Bits => (run A c P extra confidence bits).map fun (_,mask,_) => mask) =
      (fun bits : Bits => (round A c P D chosenMode extra confidence bits).map Prod.fst) := by
    funext bits
    simp only [run,found,Option.bind_some,threshold,Option.map_map]
    rfl
  rw [observed]
  exact AmplifiedSparsestVertexTape.failure A w c P τ distinct chosenMode extra confidence B Bpositive expected

end
end DirectedFlowCutGap.AmplifiedNormalizedVertexSparsest
