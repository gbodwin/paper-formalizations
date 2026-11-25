import DirectedFlowCutGap.RationalInstanceEdgeFactor
import DirectedFlowCutGap.RationalThresholdRepresentatives
import DirectedFlowCutGap.TwoSideEdgeFactor

/-! A finite rational implementation of the two-sided threshold oracle.
The candidates are sorted breakpoints and midpoints of consecutive pairs. -/
namespace DirectedFlowCutGap.RationalTwoSideOracle

open scoped NNReal NNRat BigOperators
open BinaryFractionalWalkOracle (Adjacency graph)
open RationalEdgeThresholds (Weights weights)
open RationalExactEdgeOracle (Edge arcSet arcSet_value)
open RationalEdgeDecomposition (Good originalWeight originalWeight_eq)
open RationalThresholdRepresentatives (candidates exists_representative)

variable {n : ℕ}

private def weight (A : Adjacency n) (w : Weights n) (e : Edge n) : ℚ :=
  originalWeight A w e

private def breakpoint (A : Adjacency n) (w : Weights n) (side : Edge n → Bool) (e : Edge n) : ℚ :=
  if side e then max 0 (1-weight A w e) else min 1 (weight A w e)

private theorem breakpoint_bounds (A : Adjacency n) (w : Weights n)
    (side : Edge n → Bool) (e : Edge n) : 0 ≤ breakpoint A w side e ∧ breakpoint A w side e ≤ 1 := by
  have nonneg : 0 ≤ weight A w e := (originalWeight A w e).coe_nonneg
  unfold breakpoint
  split
  · exact ⟨le_max_left ..,max_le zero_le_one (by linarith)⟩
  · exact ⟨le_min zero_le_one nonneg,min_le_left ..⟩

private def activeArcs (A : Adjacency n) : List (Edge n) :=
  (RetainedTapeInput.allPairs n).filter fun e => e ∈ arcSet A

@[simp] private theorem activeArcs_mem (A : Adjacency n) (e : Edge n) :
    e ∈ activeArcs A ↔ e ∈ arcSet A := by
  simp [activeArcs]

private def breaks (A : Adjacency n) (w : Weights n) (side : Edge n → Bool) : List ℚ :=
  0::1::(activeArcs A).map (breakpoint A w side)

def levels (A : Adjacency n) (w : Weights n) (side : Edge n → Bool) : List ℚ :=
  candidates (breaks A w side)

theorem levels_length (A : Adjacency n) (w : Weights n) (side : Edge n → Bool) :
    (levels A w side).length = 2*(arcSet A).card+3 := by
  have each : (activeArcs A).Nodup := (RetainedTapeInput.allPairs_nodup n).filter _
  have equal : (activeArcs A).toFinset = arcSet A := by ext e; simp
  have count := List.toFinset_card_of_nodup each
  rw [equal] at count
  simp only [levels,RationalThresholdRepresentatives.candidates_length,breaks,List.length_cons,
    List.length_map,← count]
  omega

private theorem breaks_bounds (A : Adjacency n) (w : Weights n) (side : Edge n → Bool)
    {q : ℚ} (listed : q ∈ breaks A w side) : 0 ≤ q ∧ q ≤ 1 := by
  simp only [breaks,List.mem_cons,List.mem_map] at listed
  rcases listed with rfl | rfl | ⟨e,_,rfl⟩
  · exact ⟨le_rfl,zero_le_one⟩
  · exact ⟨zero_le_one,le_rfl⟩
  · exact breakpoint_bounds A w side e

private theorem level_bounds (A : Adjacency n) (w : Weights n) (side : Edge n → Bool)
    {q : ℚ} (listed : q ∈ levels A w side) : 0 ≤ q ∧ q ≤ 1 :=
  RationalThresholdRepresentatives.bounds_of_mem _ (fun _ h => breaks_bounds A w side h) listed

def cut (A : Adjacency n) (w : Weights n) (side : Edge n → Bool) (q : ℚ) : Finset (Edge n) :=
  (arcSet A).filter fun e =>
    if side e then breakpoint A w side e ≤ q else q ≤ breakpoint A w side e

private theorem castWeight (A : Adjacency n) (w : Weights n) {e : Edge n} (arc : e ∈ arcSet A) :
    (weight A w e : ℝ) = (weights w e : ℝ) := by
  have actual := (mem_graphEdges (graph A) e).mp (by simpa only [arcSet_value] using arc)
  unfold weight
  rw [← actualEdgeWeight_of_adj (graph A) (weights w) actual,
    ← congrArg (fun t : ℝ≥0 => (t : ℝ)) (originalWeight_eq A w e)]
  exact map_nnratCast (Rat.castHom ℝ) (originalWeight A w e)

private theorem cut_comparison (A : Adjacency n) (w : Weights n) (side : Edge n → Bool)
    {d : ℝ} (hd : d ∈ Set.Icc (0 : ℝ) 1) (e : Edge n) :
    e ∈ TwoSideEdgeFactor.levelCut (graph A) (weights w) side d ↔
      e ∈ arcSet A ∧ if side e then (breakpoint A w side e : ℝ) ≤ d else d ≤ (breakpoint A w side e : ℝ) := by
  rw [TwoSideEdgeFactor.mem_levelCut,← arcSet_value]
  apply and_congr_right
  intro arc
  have weightEq := castWeight A w arc
  cases clr : side e
  · simp [breakpoint,clr,Rat.cast_min,weightEq,hd.2]
  · simp [breakpoint,clr,Rat.cast_max,weightEq,hd.1]

private theorem cut_real (A : Adjacency n) (w : Weights n) (side : Edge n → Bool)
    {q : ℚ} (hq : 0 ≤ q ∧ q ≤ 1) :
    cut A w side q = TwoSideEdgeFactor.levelCut (graph A) (weights w) side (q : ℝ) := by
  ext e
  have hd : (q : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by
    exact ⟨by exact_mod_cast hq.1,by exact_mod_cast hq.2⟩
  rw [cut,Finset.mem_filter,cut_comparison A w side hd e]
  exact and_congr_right fun _ => by
    cases side e <;> simp

theorem cut_good (A : Adjacency n) (w : Weights n) (side : Edge n → Bool)
    (separate : ∀ {s t : Fin n} (p : SimplePath (graph A) s t),
      Set.InjOn side (↑(p.edges.filter fun e => 0 < weights w e) : Set (Edge n)))
    {q : ℚ} (range : 0 ≤ q ∧ q ≤ 1) : Good A w (cut A w side q) := by
  rw [cut_real A w side range]
  have interval : (q : ℝ) ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨by exact_mod_cast range.1, by exact_mod_cast range.2⟩
  have valid := TwoSideEdgeFactor.levelCut_valid (graph A) (weights w) side separate interval
  exact ⟨TwoSideEdgeFactor.levelCut_actual (graph A) (weights w) side _,
    fun s t h => valid s t ((RationalEdgeThresholds.demands_iff A w _).mp h)⟩

theorem cut_half_weight (A : Adjacency n) (w : Weights n) (side : Edge n → Bool)
    {e : Edge n} (inCut : e ∈ cut A w side (1/2)) :
    (1/2 : ℝ) ≤ (originalWeight A w e : ℝ) := by
  rw [cut_real A w side (show 0 ≤ (1/2 : ℚ) ∧ (1/2 : ℚ) ≤ 1 by norm_num)] at inCut
  have test := (TwoSideEdgeFactor.mem_levelCut (graph A) (weights w) side _ e).mp inCut
  have arc := (mem_graphEdges (graph A) e).mp test.1
  have weightEq : (originalWeight A w e : ℝ) = (weights w e : ℝ) :=
    congrArg (fun value : ℝ≥0 => (value : ℝ))
      ((originalWeight_eq A w e).trans (actualEdgeWeight_of_adj (graph A) (weights w) arc))
  rw [weightEq]
  have h := test.2
  cases flag : side e
  · simpa [flag] using h
  · simp [flag] at h
    linarith

private theorem representative_cut (A : Adjacency n) (w : Weights n) (side : Edge n → Bool)
    {d : ℝ} (hd : d ∈ Set.Icc (0 : ℝ) 1) :
    ∃ q ∈ levels A w side, cut A w side q = TwoSideEdgeFactor.levelCut (graph A) (weights w) side d := by
  obtain ⟨q,listed,hq0,hq1,same⟩ := exists_representative (breaks A w side) (by simp [breaks]) (by simp [breaks]) hd.1 hd.2
  have hr : 0 ≤ q ∧ q ≤ 1 := ⟨by exact_mod_cast hq0,by exact_mod_cast hq1⟩
  have hq : (q : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨hq0,hq1⟩
  refine ⟨q,listed,?_⟩
  rw [cut_real A w side hr]
  ext e
  rw [cut_comparison A w side hq e,cut_comparison A w side hd e]
  apply and_congr_right
  intro arc
  have hmem : breakpoint A w side e ∈ breaks A w side :=
    List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_map_of_mem ((activeArcs_mem A e).mpr arc)))
  cases side e <;> simp only [Bool.false_eq_true,ite_true,ite_false]
  · exact (same _ hmem).1
  · exact (same _ hmem).2

private def fee (price : Edge n → ℚ≥0) (cut : Finset (Edge n)) : ℚ≥0 :=
  ∑ e ∈ cut, price e

def run (A : Adjacency n) (w : Weights n) (side : Edge n → Bool)
    (price : Edge n → ℚ≥0) : Option (Finset (Edge n)) :=
  ((levels A w side).map (cut A w side)).minOn? (fee price)

theorem run_spec (A : Adjacency n) (w : Weights n) (side : Edge n → Bool)
    (separate : ∀ {s t : Fin n} (p : SimplePath (graph A) s t),
      Set.InjOn side (↑(p.edges.filter fun e => 0 < weights w e) : Set (Edge n)))
    (price : Edge n → ℚ≥0) :
    ∃ X, run A w side price = some X ∧ X ⊆ graphEdges (graph A) ∧
      IsIntegralEdgeCut (graph A) X (edgeThresholdDemands (graph A) (weights w)) ∧
      (edgeCutCost (graph A) (fun e => (price e : ℝ≥0)) X : ℝ) ≤
        weightedEdgeCost (graph A) (fun e => (price e : ℝ≥0)) (weights w) := by
  let c : Edge n → ℝ≥0 := fun e => price e
  obtain ⟨d,hd,within⟩ := TwoSideEdgeFactor.exists_level_cost (graph A) (weights w) c side
  obtain ⟨q,listed,ref⟩ := representative_cut A w side hd
  let possible := (levels A w side).map (cut A w side)
  have present : cut A w side q ∈ possible := List.mem_map_of_mem listed
  let nonempty := List.ne_nil_of_mem present
  let X := possible.minOn (fee price) nonempty
  have member : X ∈ possible := List.minOn_mem
  obtain ⟨r,hr,chosen⟩ := List.mem_map.mp member
  have validRange := level_bounds A w side hr
  have real : cut A w side r = TwoSideEdgeFactor.levelCut (graph A) (weights w) side (r : ℝ) :=
    cut_real A w side validRange
  have dRange : (r : ℝ) ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨by exact_mod_cast validRange.1,by exact_mod_cast validRange.2⟩
  refine ⟨cut A w side r,?_,?_,?_,?_⟩
  · exact (List.minOn?_eq_some_minOn nonempty).trans (congrArg some chosen.symm)
  · rw [real]
    exact TwoSideEdgeFactor.levelCut_actual (graph A) (weights w) side _
  · rw [real]
    exact TwoSideEdgeFactor.levelCut_valid (graph A) (weights w) side separate dRange
  · have minimum : fee price X ≤ fee price (cut A w side q) :=
      List.apply_minOn_le_of_mem (f := fee price) present
    have compare : fee price (cut A w side r) ≤ fee price (cut A w side q) := by
      rw [chosen]
      exact minimum
    have costAt (x : ℚ) : (edgeCutCost (graph A) c (cut A w side x) : ℝ) =
        ((fee price (cut A w side x) : ℝ≥0) : ℝ) := by
      have supported : cut A w side x ⊆ graphEdges (graph A) := by
        rw [← arcSet_value]
        exact Finset.filter_subset _ _
      rw [edgeCutCost_eq_sum_of_subset (graph A) c supported]
      simp [fee,c,NNRat.cast_sum]
    change (edgeCutCost (graph A) c (cut A w side r) : ℝ) ≤ _
    rw [costAt r]
    calc
      _ ≤ ((fee price (cut A w side q) : ℝ≥0) : ℝ) :=
        by exact_mod_cast compare
      _ = (edgeCutCost (graph A) c (TwoSideEdgeFactor.levelCut (graph A) (weights w) side d) : ℝ) := by
        rw [← ref,costAt q]
      _ ≤ _ := within

/-- Use an explicitly supplied separation of positive arcs. Its feasibility
and exact cost bound are certified by `runSeparated_spec`. -/
def runSeparated (A : Adjacency n) (w : Weights n) (side : Edge n → Bool)
    (price : Edge n → ℚ≥0) : Option (Finset (Edge n)) :=
  if RationalInstanceEdgeFactor.emptyCutAccepted A w then some ∅ else run A w side price

theorem least_le_one_of_separates (A : Adjacency n) (w : Weights n) (side : Edge n → Bool)
    (separate : ∀ {s t : Fin n} (p : SimplePath (graph A) s t),
      Set.InjOn side (↑(p.edges.filter fun e => 0 < weights w e) : Set (Edge n))) :
    RationalInstanceEdgeFactor.least A w ≤ 1 := by
  apply RationalInstanceEdgeFactor.least_le_of_factor A w 1
  simpa using TwoSideEdgeFactor.factor_one (graph A) (weights w) side separate

theorem runSeparated_spec (A : Adjacency n) (w : Weights n) (side : Edge n → Bool)
    (separate : ∀ {s t : Fin n} (p : SimplePath (graph A) s t),
      Set.InjOn side (↑(p.edges.filter fun e => 0 < weights w e) : Set (Edge n)))
    (price : Edge n → ℚ≥0) :
    ∃ X, runSeparated A w side price = some X ∧ X ⊆ graphEdges (graph A) ∧
      IsIntegralEdgeCut (graph A) X (edgeThresholdDemands (graph A) (weights w)) ∧
      (edgeCutCost (graph A) (fun e => (price e : ℝ≥0)) X : ℝ) ≤
        (RationalInstanceEdgeFactor.least A w : ℝ) *
          (weightedEdgeCost (graph A) (fun e => (price e : ℝ≥0)) (weights w) : ℝ) := by
  by_cases emptyAccepted : RationalInstanceEdgeFactor.emptyCutAccepted A w = true
  · have zero := (RationalInstanceEdgeFactor.emptyCutAccepted_zero A w).mp emptyAccepted
    have valid := (RationalInstanceEdgeFactor.emptyCutAccepted_iff A w).mp emptyAccepted
    refine ⟨∅,by simp [runSeparated,emptyAccepted],Finset.empty_subset _,valid,?_⟩
    simp [zero,edgeCutCost]
  · have positive : 1 ≤ RationalInstanceEdgeFactor.least A w :=
      Nat.one_le_iff_ne_zero.mpr fun h =>
        emptyAccepted ((RationalInstanceEdgeFactor.emptyCutAccepted_zero A w).mpr h)
    have one := Nat.le_antisymm (least_le_one_of_separates A w side separate) positive
    obtain ⟨X,read,arcs,valid,paid⟩ := run_spec A w side separate price
    refine ⟨X,?_,arcs,valid,?_⟩
    · simpa [runSeparated,emptyAccepted] using read
    · simpa [one] using paid

def runEndpoint (A : Adjacency n) (w : Weights n) (price : Edge n → ℚ≥0) :
    Option (Finset (Edge n)) :=
  if RationalInstanceEdgeFactor.endpointCap A w ≤ 2 then
    runSeparated A w (RationalInstanceEdgeFactor.endpointSides A w) price
  else none

theorem runEndpoint_above_cap (A : Adjacency n) (w : Weights n)
    (price : Edge n → ℚ≥0) (big : 2 < RationalInstanceEdgeFactor.endpointCap A w) :
    runEndpoint A w price = none := by
  simp [runEndpoint,not_le_of_gt big]

theorem runEndpoint_spec (A : Adjacency n) (w : Weights n)
    (small : RationalInstanceEdgeFactor.endpointCap A w ≤ 2) (price : Edge n → ℚ≥0) :
    ∃ X, runEndpoint A w price = some X ∧ X ⊆ graphEdges (graph A) ∧
      IsIntegralEdgeCut (graph A) X (edgeThresholdDemands (graph A) (weights w)) ∧
      (edgeCutCost (graph A) (fun e => (price e : ℝ≥0)) X : ℝ) ≤
        (RationalInstanceEdgeFactor.least A w : ℝ) *
          (weightedEdgeCost (graph A) (fun e => (price e : ℝ≥0)) (weights w) : ℝ) := by
  simpa [runEndpoint,small] using runSeparated_spec A w (RationalInstanceEdgeFactor.endpointSides A w)
    (fun p => RationalInstanceEdgeFactor.endpointSides_spec A w small p) price

end DirectedFlowCutGap.RationalTwoSideOracle
