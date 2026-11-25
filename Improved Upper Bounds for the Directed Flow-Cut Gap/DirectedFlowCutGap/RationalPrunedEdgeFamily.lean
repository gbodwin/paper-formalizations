import DirectedFlowCutGap.RationalPositiveArcEdgeFamily
import DirectedFlowCutGap.ExactEdgeWeightPadding

/-! Remove weights one at a time whenever the original threshold demands
survive. The resulting family uses the number of retained positive arcs. -/
namespace DirectedFlowCutGap.RationalPrunedEdgeFamily

open scoped BigOperators NNReal NNRat
open BinaryFractionalWalkOracle (Adjacency graph)
open RationalEdgeThresholds (Weights weights demands)
open RationalEdgeDecomposition (Good originalWeight originalWeight_eq originalTotal)
open RationalExactEdgeOracle (Edge)
open RationalOriginalEdgeFamily (horizon)
open RationalPositiveArcEdgeFamily (count)
open ExactFlowCutGap (efg)

variable {n : ℕ}

def clear (q : Weights n) (e : Edge n) : Weights n :=
  Vector.ofFn fun s => Vector.ofFn fun t =>
    if (s,t)=e then BinaryRational.zero else (q.get s).get t

theorem clear_weight (A : Adjacency n) (q : Weights n) (e f : Edge n) :
    originalWeight A (clear q e) f = if f=e then 0 else originalWeight A q f := by
  rcases f with ⟨s,t⟩
  by_cases chosen : (s,t)=e
  · simp only [chosen,ite_true]
    simp [originalWeight,RationalEdgeDecomposition.weightQ,BinaryFractionalWalkOracle.decodeCost,
      RationalEdgeThresholds.cost,clear,BinaryRational.decode,BinaryRational.zero,BinaryArithmetic.value]
  · simp [originalWeight,RationalEdgeDecomposition.weightQ,BinaryFractionalWalkOracle.decodeCost,
      RationalEdgeThresholds.cost,clear,chosen]
    rfl

theorem clear_le (A : Adjacency n) (q : Weights n) (e f : Edge n) :
    originalWeight A (clear q e) f ≤ originalWeight A q f := by
  rw [clear_weight]
  split
  · exact zero_le
  · exact le_rfl

def preserves (A : Adjacency n) (w q : Weights n) : Bool :=
  decide (demands A w ⊆ demands A q)

def tryClear (A : Adjacency n) (w q : Weights n) (e : Edge n) : Weights n :=
  let removed := clear q e
  if preserves A w removed then removed else q

private theorem tryClear_spec (A : Adjacency n) (w q : Weights n) (e : Edge n)
    (included : demands A w ⊆ demands A q) :
    (demands A w ⊆ demands A (tryClear A w q e)) ∧
      ∀ f, originalWeight A (tryClear A w q e) f ≤ originalWeight A q f := by
  by_cases pass : preserves A w (clear q e) = true
  · have keep : demands A w ⊆ demands A (clear q e) := of_decide_eq_true pass
    simp only [tryClear,pass,ite_true]
    exact ⟨keep,clear_le A q e⟩
  · rw [show tryClear A w q e = q from ite_eq_right pass]
    exact ⟨included,fun _ => le_rfl⟩

def indices (n : ℕ) : List (Edge n) :=
  (List.finRange n).flatMap fun s => (List.finRange n).map fun t => (s,t)

def pruned (A : Adjacency n) (w : Weights n) : Weights n :=
  (indices n).foldl (tryClear A w) w

private theorem fold_spec (A : Adjacency n) (w q : Weights n) (arcs : List (Edge n))
    (included : demands A w ⊆ demands A q) :
    let trimmed := arcs.foldl (tryClear A w) q
    (demands A w ⊆ demands A trimmed) ∧ ∀ f, originalWeight A trimmed f ≤ originalWeight A q f := by
  induction arcs generalizing q with
  | nil => exact ⟨included,fun _ => le_rfl⟩
  | cons e es ih =>
    obtain ⟨kept,smaller⟩ := tryClear_spec A w q e included
    obtain ⟨result,bound⟩ := ih (tryClear A w q e) kept
    exact ⟨result,fun f => (bound f).trans (smaller f)⟩

theorem pruned_spec (A : Adjacency n) (w : Weights n) :
    (demands A w ⊆ demands A (pruned A w)) ∧
      ∀ f, originalWeight A (pruned A w) f ≤ originalWeight A w f :=
  fold_spec A w w (indices n) (by intro _ h; exact h)

private theorem demands_mono (A : Adjacency n) {q r : Weights n}
    (bound : ∀ e, originalWeight A q e ≤ originalWeight A r e) : demands A q ⊆ demands A r := by
  intro demand found
  apply (RationalEdgeThresholds.demands_iff A r demand).mpr
  have eligible := (RationalEdgeThresholds.demands_iff A q demand).mp found
  exact eligible.trans (edgeDistance_mono (graph A) demand.1 demand.2 fun s t arc => by
    have weight : (originalWeight A q (s,t) : ℝ≥0) ≤ (originalWeight A r (s,t) : ℝ≥0) := by
      exact_mod_cast bound (s,t)
    simpa only [originalWeight_eq,actualEdgeWeight_of_adj _ _ (e:=(s,t)) arc] using weight)

theorem pruned_demands (A : Adjacency n) (w : Weights n) (e : Edge n) :
    e ∈ demands A (pruned A w) ↔ e ∈ demands A w :=
  ⟨fun h => demands_mono A (pruned_spec A w).2 h,fun h => (pruned_spec A w).1 h⟩

private theorem clear_mono (A : Adjacency n) {q r : Weights n} (e : Edge n)
    (bound : ∀ f, originalWeight A q f ≤ originalWeight A r f) (f : Edge n) :
    originalWeight A (clear q e) f ≤ originalWeight A (clear r e) f := by
  rw [clear_weight,clear_weight]
  split
  · exact le_rfl
  · exact bound f

private theorem fold_retained (A : Adjacency n) (w q : Weights n) (arcs : List (Edge n))
    (included : demands A w ⊆ demands A q) :
    let result := arcs.foldl (tryClear A w) q
    ∀ e ∈ arcs, 0 < originalWeight A result e → ¬ demands A w ⊆ demands A (clear result e) := by
  induction arcs generalizing q with
  | nil => simp
  | cons f rest ih =>
    dsimp only [List.foldl_cons]
    intro e visit positive clearing
    obtain ⟨forward,shrunk⟩ := tryClear_spec A w q f included
    rcases List.mem_cons.mp visit with same | later
    · subst e
      have reduced := (fold_spec A w (tryClear A w q f) rest forward).2
      have narrowed (g : Edge n) := (reduced g).trans (shrunk g)
      have original : demands A w ⊆ demands A (clear q f) := by
        intro g required
        exact demands_mono A (clear_mono A f narrowed) (clearing required)
      have yes : preserves A w (clear q f) = true := by
        simpa only [preserves,decide_eq_true_eq] using original
      have erased : originalWeight A (tryClear A w q f) f = 0 := by
        rw [tryClear,ite_eq_left yes,clear_weight,ite_eq_left rfl]
      exact (not_lt_of_ge ((reduced f).trans_eq erased)) positive
    · exact ih (tryClear A w q f) forward e later positive clearing

theorem retained_necessary (A : Adjacency n) (w : Weights n) (e : Edge n)
    (positive : 0 < originalWeight A (pruned A w) e) :
    ¬ demands A w ⊆ demands A (clear (pruned A w) e) :=
  fold_retained A w w (indices n) (by intro _ hit; exact hit) e
    (List.mem_flatMap.mpr ⟨e.1,List.mem_finRange _,List.mem_map.mpr ⟨e.2,List.mem_finRange _,rfl⟩⟩)
    positive

theorem positive_count (A : Adjacency n) (w : Weights n) : count A (pruned A w) ≤ count A w := by
  apply max_le_max_left
  apply Finset.card_le_card
  intro e he
  simp only [RationalPositiveArcEdgeFamily.positiveArcs,Finset.mem_filter,Finset.mem_univ,true_and] at he ⊢
  exact he.trans_le ((pruned_spec A w).2 e)

private theorem total_le (A : Adjacency n) (w : Weights n) :
    totalEdgeWeight (graph A) (weights (pruned A w)) ≤ totalEdgeWeight (graph A) (weights w) := by
  apply Finset.sum_le_sum
  intro e he
  have arc := (mem_graphEdges _ _).mp he
  have inequality : (originalWeight A (pruned A w) e : ℝ≥0) ≤
      (originalWeight A w e : ℝ≥0) := by exact_mod_cast (pruned_spec A w).2 e
  rwa [originalWeight_eq,originalWeight_eq,actualEdgeWeight_of_adj _ _ arc,actualEdgeWeight_of_adj _ _ arc] at inequality

def familyFor (A : Adjacency n) (w : Weights n) : RationalWeakFamily.History (Edge n) :=
  let α : ℚ≥0 := RationalInstanceEdgeFactor.leastMinimal A w
  if α = 0 then RationalOriginalEdgeFamily.adaptive A w α
  else RationalOriginalEdgeFamily.build A w α (count A w)

theorem familyFor_reference (A : Adjacency n) (w : Weights n) :
    familyFor A w = RationalPositiveArcEdgeFamily.family A w := by
  rw [familyFor,RationalInstanceEdgeFactor.leastMinimal_eq]
  rfl

def family (A : Adjacency n) (w : Weights n) : RationalWeakFamily.History (Edge n) :=
  familyFor A (pruned A w)

theorem family_reference (A : Adjacency n) (w : Weights n) :
    family A w = RationalPositiveArcEdgeFamily.family A (pruned A w) :=
  familyFor_reference A (pruned A w)

theorem family_nonempty (A : Adjacency n) (w : Weights n) : 0 < (family A w).cuts.length := by
  rw [family_reference]
  exact RationalPositiveArcEdgeFamily.family_nonempty A (pruned A w)

theorem length_le (hn : 0 < n) (A : Adjacency n) (w : Weights n) :
    let α := efg n (totalEdgeWeight (graph A) (weights w))
    (family A w).cuts.length ≤ horizon A w (α : ℚ≥0) (count A (pruned A w)) := by
  rw [family_reference]
  refine (RationalPositiveArcEdgeFamily.length_le_original_factor A (pruned A w)).trans ?_
  have mass : originalTotal A (pruned A w) ≤ originalTotal A w :=
    Finset.sum_le_sum fun e _ => (pruned_spec A w).2 e
  have alpha : (efg n (totalEdgeWeight (graph A) (weights (pruned A w))) : ℚ≥0) ≤
      (efg n (totalEdgeWeight (graph A) (weights w)) : ℚ≥0) :=
    Nat.cast_le.mpr (ExactFlowCutGap.efg_mono_weight hn (total_le A w))
  unfold horizon RationalWeakFamily.edgeRounds RationalWeakFamily.edgeMagnitude
  apply Nat.add_le_add_right
  apply Nat.mul_le_mul_left
  apply Nat.size_le_size
  apply Nat.ceil_mono
  gcongr

theorem length_le_vertex_horizon (hn : 0 < n) (A : Adjacency n) (w : Weights n)
    (small : count A (pruned A w) ≤ n) :
    let α := efg n (totalEdgeWeight (graph A) (weights w))
    (family A w).cuts.length ≤ horizon A w (α : ℚ≥0) n := by
  refine (length_le hn A w).trans ?_
  unfold horizon RationalWeakFamily.edgeRounds RationalWeakFamily.edgeMagnitude
  apply Nat.add_le_add_right
  apply Nat.mul_le_mul (Nat.mul_le_mul_left 2 small)
  apply Nat.size_le_size
  apply Nat.ceil_mono
  gcongr

private theorem loss_le (hn : 0 < n) (A : Adjacency n) (w : Weights n) (e : Edge n) :
    8*(originalWeight A (pruned A w) e : ℝ)*(efg n (totalEdgeWeight (graph A) (weights (pruned A w))) : ℝ) ≤
      8*(originalWeight A w e : ℝ)*(efg n (totalEdgeWeight (graph A) (weights w)) : ℝ) := by
  have alpha : (efg n (totalEdgeWeight (graph A) (weights (pruned A w))) : ℝ) ≤
      (efg n (totalEdgeWeight (graph A) (weights w)) : ℝ) :=
    Nat.cast_le.mpr (ExactFlowCutGap.efg_mono_weight hn (total_le A w))
  have weight : (originalWeight A (pruned A w) e : ℝ) ≤ (originalWeight A w e : ℝ) := by
    exact_mod_cast (pruned_spec A w).2 e
  gcongr

theorem family_spec (hn : 0 < n) (A : Adjacency n) (w : Weights n) :
    let L := (family A w).cuts
    (∀ cut ∈ L, Good A w cut) ∧
      ∀ e, (L.countP (fun cut => decide (e ∈ cut)) : ℝ)/(L.length : ℝ) ≤
        8*(originalWeight A w e : ℝ)*(efg n (totalEdgeWeight (graph A) (weights w)) : ℝ) := by
  rw [family_reference]
  have support := RationalPositiveArcEdgeFamily.family_spec A (pruned A w)
  refine ⟨?_,fun e => (support.2 e).trans (loss_le hn A w e)⟩
  intro cut member
  obtain ⟨arcs,hit⟩ := support.1 cut member
  exact ⟨arcs,fun s t requested => hit s t ((pruned_spec A w).1 requested)⟩

def draw (A : Adjacency n) (w : Weights n) (trials : ℕ) (tape : List Bool) :
    Option ((Option (Finset (Edge n)) × ℕ) × EncodedSolverBits.Tape) :=
  EncodedSolverBits.run (BinaryFamilySampler.choose (family A w).cuts trials) tape

theorem draw_reference (A : Adjacency n) (w : Weights n) (trials : ℕ) (tape : List Bool) :
    draw A w trials tape = RationalPositiveArcEdgeFamily.draw A (pruned A w) trials tape := by
  simp only [draw,family_reference,RationalPositiveArcEdgeFamily.draw]

theorem draw_used (A : Adjacency n) (w : Weights n) (trials : ℕ) (tape : List Bool)
    (enough : trials*FairBitWords.width (family A w).cuts.length ≤ tape.length) :
    ∃ cut paid used, draw A w trials tape = some ((cut,paid),(tape.drop used,used)) ∧
      used ≤ trials*FairBitWords.width (family A w).cuts.length := by
  rw [family_reference] at enough ⊢
  simpa only [draw_reference] using RationalPositiveArcEdgeFamily.draw_used A (pruned A w) trials tape enough

theorem draw_valid (A : Adjacency n) (w : Weights n) {trials : ℕ} {tape rest : List Bool}
    {cut : Finset (Edge n)} {paid used : ℕ}
    (played : draw A w trials tape = some ((some cut,paid),(rest,used))) : Good A w cut := by
  rw [draw_reference] at played
  obtain ⟨arcs,valid⟩ := RationalPositiveArcEdgeFamily.draw_valid A (pruned A w) played
  exact ⟨arcs,fun s t requested => valid s t ((pruned_spec A w).1 requested)⟩

theorem draw_law (hn : 0 < n) (A : Adjacency n) (w : Weights n) (trials : ℕ) :
    let L := (family A w).cuts
    let Q := trials*FairBitWords.width L.length
    let p := (EncodedSolverBits.fairTape Q).map (fun tape => ((draw A w trials tape).map (fun r => r.1.1)).join)
    p none = BoundedBitRejection.law L.length trials none ∧
      ∀ e, FiniteAmplification.probability p (fun o => ∃ cut ∈ o, e ∈ cut) ≤
        8*(originalWeight A w e : ℝ)*(efg n (totalEdgeWeight (graph A) (weights w)) : ℝ) := by
  dsimp only
  rw [family_reference A w]
  simp only [draw_reference]
  have law := RationalPositiveArcEdgeFamily.draw_law A (pruned A w) trials
  exact ⟨law.1,fun e => (law.2 e).trans (loss_le hn A w e)⟩

end DirectedFlowCutGap.RationalPrunedEdgeFamily
