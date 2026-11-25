import DirectedFlowCutGap.BinaryRawRational
import DirectedFlowCutGap.RationalPrunedEdgeFamily
import DirectedFlowCutGap.RationalTrimmedEdgeFamily

/-! Spend the weight freed by light-arc trimming on a uniform rescaling
of the retained arcs. Test the original demands in the same graph and
use the arc-by-arc family if the test fails. -/
namespace DirectedFlowCutGap.RationalBudgetedRescaleEdgeFamily

open scoped BigOperators ENNReal NNRat NNReal
open BinaryFractionalWalkOracle (Adjacency graph decodeCost)
open RationalEdgeThresholds (Weights weights cost demands demands_iff)
open RationalExactEdgeOracle (Edge)
open RationalEdgeDecomposition (Good originalWeight originalWeight_eq originalTotal weightQ)
open RationalTrimmedEdgeFamily (cutoff trimmed trimmed_weight_le cutoff_lt_of_trimmed_positive)
open RationalOriginalEdgeFamily (adaptive chooseScale floor lightMass horizon)
open RationalPrunedEdgeFamily (preserves pruned)
open ExactFlowCutGap (efg)

variable {n : ℕ}

private def fixedWeight (r : ℚ≥0) : ℚ≥0 := if 1 ≤ r then 1 else 0

private def scalableWeight (r : ℚ≥0) : ℚ≥0 := if 1 ≤ r then 0 else r

private def fixedTotal (A : Adjacency n) (w : Weights n) : ℚ≥0 :=
  ∑ e, fixedWeight (originalWeight A (trimmed A w) e)

private def scalableTotal (A : Adjacency n) (w : Weights n) : ℚ≥0 :=
  ∑ e, scalableWeight (originalWeight A (trimmed A w) e)

/-- Reserve length one for each already saturated arc. Scale the remaining
positive lengths as far as their remaining budget and the cap of two allow. -/
def multiplier (A : Adjacency n) (w : Weights n) : ℚ≥0 :=
  let amount := scalableTotal A w
  if amount = 0 then 1 else min 2 ((originalTotal A w - fixedTotal A w) / amount)

theorem multiplier_from_sums (A : Adjacency n) (w : Weights n) :
    let r (e : Edge n) := originalWeight A (trimmed A w) e
    let fixed := ∑ e, if 1 ≤ r e then (1 : ℚ≥0) else 0
    let subunit := ∑ e, if 1 ≤ r e then (0 : ℚ≥0) else r e
    multiplier A w = if subunit = 0 then 1 else min 2 ((originalTotal A w - fixed) / subunit) :=
  rfl

private theorem capped_total_le (A : Adjacency n) (w : Weights n) :
    fixedTotal A w + scalableTotal A w ≤ originalTotal A w := by
  unfold fixedTotal scalableTotal originalTotal
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun e _ => ?_
  have within := trimmed_weight_le A w e
  by_cases large : 1 ≤ originalWeight A (trimmed A w) e
  · simpa [fixedWeight,scalableWeight,large] using large.trans within
  · simpa [fixedWeight,scalableWeight,large] using within

private theorem multiplier_spec (A : Adjacency n) (w : Weights n) :
    1 ≤ multiplier A w ∧ multiplier A w ≤ 2 ∧
      fixedTotal A w + multiplier A w * scalableTotal A w ≤ originalTotal A w := by
  have capped := capped_total_le A w
  have fixed_le : fixedTotal A w ≤ originalTotal A w := (self_le_add_right _ _).trans capped
  unfold multiplier
  dsimp only
  split
  · rename_i empty
    simp only [empty,mul_zero,add_zero]
    exact ⟨le_rfl,by norm_num,fixed_le⟩
  · rename_i nonzero
    have positive := pos_iff_ne_zero.mpr nonzero
    have budget : scalableTotal A w ≤ originalTotal A w - fixedTotal A w := by
      apply (le_tsub_iff_right fixed_le).mpr
      simpa [add_comm] using capped
    refine ⟨le_min (by norm_num) ((le_div_iff₀ positive).mpr (by simpa using budget)),min_le_left ..,?_⟩
    have cap := min_le_right (2 : ℚ≥0) ((originalTotal A w - fixedTotal A w) / scalableTotal A w)
    have nonneg : 0 ≤ scalableTotal A w := zero_le
    calc
      _ ≤ fixedTotal A w + ((originalTotal A w - fixedTotal A w) / scalableTotal A w) * scalableTotal A w :=
        add_le_add_right (mul_le_mul_of_nonneg_right cap nonneg) _
      _ = _ := by
        rw [div_mul_cancel₀ _ nonzero,add_comm,tsub_add_cancel_of_le fixed_le]

/-- Keep arcs already reaching threshold at one and scale the other weights. -/
def scaledWeight (g r : ℚ≥0) : ℚ≥0 := if 1 ≤ r then 1 else g * r

private theorem scaledWeight_eq (g r : ℚ≥0) : scaledWeight g r = fixedWeight r + g * scalableWeight r := by
  by_cases large : 1 ≤ r <;> simp [large,scaledWeight,fixedWeight,scalableWeight]

def rescaled (A : Adjacency n) (w : Weights n) : Weights n :=
  let g := multiplier A w
  let q := trimmed A w
  Vector.ofFn fun u => Vector.ofFn fun v =>
    (BinaryRawRational.encode
      (RawNonnegativeRational.Code.ofNNRat (scaledWeight g (originalWeight A q (u,v))))).1

theorem rescaled_weight (A : Adjacency n) (w : Weights n) (e : Edge n) :
    originalWeight A (rescaled A w) e = scaledWeight (multiplier A w) (originalWeight A (trimmed A w) e) := by
  rcases e with ⟨u,v⟩
  by_cases edge : A[u.val][v.val] = true
  · simp [originalWeight,edge,rescaled,weightQ,decodeCost,cost,BinaryRawRational.encode_eq]
  · simp [originalWeight,edge,scaledWeight]

theorem rescaled_total_le (A : Adjacency n) (w : Weights n) :
    originalTotal A (rescaled A w) ≤ originalTotal A w := by
  simp only [originalTotal,rescaled_weight,scaledWeight_eq,Finset.sum_add_distrib,← Finset.mul_sum]
  exact (multiplier_spec A w).2.2

theorem rescaled_weight_le (A : Adjacency n) (w : Weights n) (e : Edge n) :
    originalWeight A (rescaled A w) e ≤ 2 * originalWeight A w e := by
  rw [rescaled_weight,scaledWeight]
  split
  · rename_i large
    have factor : (1 : ℚ≥0) ≤ 2 := by norm_num
    have nonneg : 0 ≤ originalWeight A w e := zero_le
    have doubled : originalWeight A w e ≤ 2 * originalWeight A w e := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right factor nonneg
    exact (large.trans (trimmed_weight_le A w e)).trans doubled
  · exact mul_le_mul' (multiplier_spec A w).2.1 (trimmed_weight_le A w e)

private theorem rescaled_floor (hn : 0 < n) (A : Adjacency n) (w : Weights n) (e : Edge n)
    (positive : 0 < originalWeight A (rescaled A w) e) :
    cutoff n < originalWeight A (rescaled A w) e := by
  rw [rescaled_weight,scaledWeight] at positive ⊢
  by_cases large : 1 ≤ originalWeight A (trimmed A w) e
  · rw [ite_eq_left large]
    have one : (1 : ℚ≥0) ≤ n := by exact_mod_cast hn
    have two := mul_le_mul_of_nonneg_left one (by norm_num : (0 : ℚ≥0) ≤ 2)
    unfold cutoff
    apply (inv_lt_one₀ (by positivity)).mpr
    exact (by norm_num : (1 : ℚ≥0) < 2 * 1).trans_le two
  · rw [ite_eq_right large] at positive ⊢
    have kept := pos_of_mul_pos_right positive zero_le
    have above := cutoff_lt_of_trimmed_positive A w e kept
    refine above.trans_le ?_
    simpa using mul_le_mul_of_nonneg_right (multiplier_spec A w).1 kept.le

def eligible (A : Adjacency n) (w : Weights n) : Bool :=
  preserves A w (rescaled A w)

theorem eligible_iff (A : Adjacency n) (w : Weights n) :
    eligible A w = true ↔ demands A w ⊆ demands A (rescaled A w) := by
  simp [eligible,preserves]

private theorem rescaled_dominates_clipped (A : Adjacency n) (w : Weights n) (e : Edge n) :
    min 1 (originalWeight A (trimmed A w) e) ≤ originalWeight A (rescaled A w) e := by
  rw [rescaled_weight,scaledWeight]
  split
  · exact min_le_left ..
  · have nonneg : 0 ≤ originalWeight A (trimmed A w) e := zero_le
    have enlarged : originalWeight A (trimmed A w) e ≤ multiplier A w * originalWeight A (trimmed A w) e := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right (multiplier_spec A w).1 nonneg
    exact (min_le_right ..).trans enlarged

theorem eligible_of_trimmed (A : Adjacency n) (w : Weights n)
    (held : RationalTrimmedEdgeFamily.keepsDemands A w = true) : eligible A w = true := by
  apply (eligible_iff A w).mpr
  rintro ⟨s,t⟩ original
  apply (demands_iff A _ (s,t)).mpr
  apply (coe_le_edgeDistance_iff (graph A) (weights (rescaled A w)) s t 1).mpr
  intro path
  have requested := (RationalTrimmedEdgeFamily.keepsDemands_value A w).mp held
    ((demands_iff A w (s,t)).mp original)
  have old := (coe_le_edgeDistance_iff (graph A) (weights (trimmed A w)) s t 1).mp requested path
  refine (ExactFlowCutGap.one_le_clamped_path path (weights (trimmed A w)) old).trans ?_
  refine Finset.sum_le_sum fun e member => ?_
  have edge := path.edge_adj member
  rw [← actualEdgeWeight_of_adj (graph A) (weights (trimmed A w)) edge,
    ← actualEdgeWeight_of_adj (graph A) (weights (rescaled A w)) edge,
    ← originalWeight_eq, ← originalWeight_eq]
  exact_mod_cast rescaled_dominates_clipped A w e

private theorem originalTotal_real (A : Adjacency n) (w : Weights n) :
    (originalTotal A w : ℝ≥0) = totalEdgeWeight (graph A) (weights w) := by
  simp only [originalTotal,NNRat.cast_sum,originalWeight_eq]
  apply NNReal.coe_injective
  rw [NNReal.coe_sum]
  exact WeakDecomposition.sum_actualEdgeWeight (graph A) (weights w)

private def factor (A : Adjacency n) (q : Weights n) : ℚ≥0 :=
  RationalInstanceEdgeFactor.leastSupported A q

private theorem factor_valid (A : Adjacency n) (q : Weights n) :
    HasEdgeRoundingFactor (graph A) (weights q) (factor A q : ℝ) := by
  simpa only [factor,RationalInstanceEdgeFactor.leastSupported_eq,NNRat.cast_natCast] using
    RationalInstanceEdgeFactor.least_valid A q

private theorem factor_le (hn : 0 < n) (A : Adjacency n) (w : Weights n) :
    factor A (rescaled A w) ≤ (efg n (totalEdgeWeight (graph A) (weights w)) : ℚ≥0) := by
  unfold factor
  rw [RationalInstanceEdgeFactor.leastSupported_eq]
  apply Nat.cast_le.mpr
  apply RationalInstanceEdgeFactor.least_le_of_factor
  apply ExactFlowCutGap.efg_round_atMost hn
  rw [← originalTotal_real A (rescaled A w),← originalTotal_real A w,NNRat.cast_le]
  exact rescaled_total_le A w

def family (A : Adjacency n) (w : Weights n) : RationalWeakFamily.History (Edge n) :=
  let q := rescaled A w
  if preserves A w q then adaptive A q (factor A q)
  else RationalPrunedEdgeFamily.family A w

theorem family_nonempty (A : Adjacency n) (w : Weights n) : 0 < (family A w).cuts.length := by
  unfold family
  dsimp only
  split
  · exact RationalOriginalEdgeFamily.adaptive_nonempty ..
  · exact RationalPrunedEdgeFamily.family_nonempty ..

theorem family_spec (hn : 0 < n) (A : Adjacency n) (w : Weights n) :
    let L := (family A w).cuts
    (∀ X ∈ L, Good A w X) ∧
      ∀ e, (L.countP (fun X => decide (e ∈ X)) : ℝ) / (L.length : ℝ) ≤
        16 * (originalWeight A w e : ℝ) * (efg n (totalEdgeWeight (graph A) (weights w)) : ℝ) := by
  unfold family
  dsimp only
  split
  · rename_i allowed
    let q := rescaled A w
    have h := RationalOriginalEdgeFamily.adaptive_spec_all hn A q _ (factor_valid A q)
    refine ⟨?_,fun e => (h.2 e).trans ?_⟩
    · intro X listed
      obtain ⟨edges,cut⟩ := h.1 X listed
      exact ⟨edges,fun s t demand => cut s t ((eligible_iff A w).mp allowed demand)⟩
    · have price : (factor A q : ℝ) ≤ (efg n (totalEdgeWeight (graph A) (weights w)) : ℝ) := by
        exact_mod_cast factor_le hn A w
      have wgt : (originalWeight A q e : ℝ) ≤ 2 * (originalWeight A w e : ℝ) := by
        exact_mod_cast rescaled_weight_le A w e
      calc
        _ ≤ 8 * (2 * (originalWeight A w e : ℝ)) * (efg n (totalEdgeWeight (graph A) (weights w)) : ℝ) := by
          gcongr
        _ = _ := by ring
  · have h := RationalPrunedEdgeFamily.family_spec hn A w
    refine ⟨h.1,fun e => (h.2 e).trans ?_⟩
    gcongr
    norm_num

private theorem rescaled_scale (hn : 0 < n) (A : Adjacency n) (w : Weights n)
    (positive : 0 < factor A (rescaled A w)) :
    chooseScale A (rescaled A w) (factor A (rescaled A w)) = n := by
  let q := rescaled A w
  let a := factor A q
  have alpha : (1 : ℚ≥0) ≤ a := by
    change (1 : ℚ≥0) ≤ (RationalInstanceEdgeFactor.leastSupported A q : ℚ≥0)
    exact_mod_cast (Nat.succ_le_of_lt (Nat.cast_pos.mp
      (show 0 < (RationalInstanceEdgeFactor.leastSupported A q : ℚ≥0) from positive)))
  have floor_le : floor n a ≤ cutoff n := by
    unfold floor cutoff
    apply (inv_le_inv₀ (by positivity) (by positivity)).mpr
    calc
      (2 : ℚ≥0) * n ≤ 4 * n := mul_le_mul_of_nonneg_right (by norm_num) zero_le
      _ ≤ 4 * a * n := by simpa using
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left alpha (by norm_num : (0 : ℚ≥0) ≤ 4)) (Nat.cast_nonneg n)
  have zero_mass : lightMass A q a n = 0 := by
    unfold lightMass
    rw [Finset.sum_eq_zero,mul_zero]
    intro e member
    have light := (Finset.mem_filter.mp member).2
    by_contra nonzero
    have above := rescaled_floor hn A w e (pos_iff_ne_zero.mpr nonzero)
    exact (not_lt_of_ge floor_le) (above.trans light)
  change (if lightMass A q a n ≤ 1/4 then n else _) = n
  rw [zero_mass,ite_eq_left (by positivity : (0 : ℚ≥0) ≤ 1/4)]

theorem length_le_vertex_horizon (hn : 0 < n) (A : Adjacency n) (w : Weights n)
    (enough : eligible A w = true ∨ RationalPositiveArcEdgeFamily.count A (pruned A w) ≤ n) :
    let α := efg n (totalEdgeWeight (graph A) (weights w))
    (family A w).cuts.length ≤ horizon A w (α : ℚ≥0) n := by
  unfold family
  dsimp only
  split
  · let q := rescaled A w
    let a := factor A q
    by_cases h : a = 0
    · rw [adaptive,ite_eq_left h]
      exact RationalWeakFamily.edgeRounds_pos ..
    · rw [adaptive,ite_eq_right h,RationalOriginalEdgeFamily.build_length,rescaled_scale hn A w (pos_iff_ne_zero.mpr h)]
      have lower := factor_le hn A w
      have budget := rescaled_total_le A w
      unfold horizon RationalWeakFamily.edgeRounds RationalWeakFamily.edgeMagnitude
      apply Nat.add_le_add_right
      apply Nat.mul_le_mul_left
      apply Nat.size_le_size
      apply Nat.ceil_mono
      gcongr
  · rename_i rejected
    exact RationalPrunedEdgeFamily.length_le_vertex_horizon hn A w (enough.resolve_left rejected)

def draw (A : Adjacency n) (w : Weights n) (trials : ℕ) (tape : List Bool) :
    Option ((Option (Finset (Edge n)) × ℕ) × EncodedSolverBits.Tape) :=
  EncodedSolverBits.run (BinaryFamilySampler.choose (family A w).cuts trials) tape

theorem draw_used (A : Adjacency n) (w : Weights n) (trials : ℕ) (tape : List Bool)
    (enough : trials * FairBitWords.width (family A w).cuts.length ≤ tape.length) :
    ∃ cut paid used, draw A w trials tape = some ((cut,paid),(tape.drop used,used)) ∧
      used ≤ trials * FairBitWords.width (family A w).cuts.length :=
  BinaryFamilySampler.choose_used _ _ _ enough

theorem draw_valid (hn : 0 < n) (A : Adjacency n) (w : Weights n) {trials : ℕ}
    {tape rest : List Bool} {cut : Finset (Edge n)} {paid used : ℕ}
    (played : draw A w trials tape = some ((some cut,paid),(rest,used))) : Good A w cut := by
  let cuts := (family A w).cuts
  have seen := EncodedSolverBits.run_support (BinaryFamilySampler.choose_binary cuts trials) played
  have inList := (BinaryFamilySampler.choose_supported cuts trials seen).1 cut (by simp)
  exact (family_spec hn A w).1 cut inList

theorem draw_law (hn : 0 < n) (A : Adjacency n) (w : Weights n) (trials : ℕ) :
    let cuts := (family A w).cuts
    let q := trials * FairBitWords.width cuts.length
    let p := (EncodedSolverBits.fairTape q).map (fun tape => ((draw A w trials tape).map (fun r => r.1.1)).join)
    p none = BoundedBitRejection.law cuts.length trials none ∧
      ∀ e, FiniteAmplification.probability p (fun o => ∃ X ∈ o, e ∈ X) ≤
        16 * (originalWeight A w e : ℝ) * (efg n (totalEdgeWeight (graph A) (weights w)) : ℝ) := by
  let cuts := (family A w).cuts
  let q := trials * FairBitWords.width cuts.length
  let p := (EncodedSolverBits.fairTape q).map (fun tape => ((draw A w trials tape).map (fun r => r.1.1)).join)
  change p none = _ ∧ ∀ e, FiniteAmplification.probability p (fun o => ∃ X ∈ o, e ∈ X) ≤ _
  have eq : p = (FiniteDrawTrees.ideal (BinaryFamilySampler.choose cuts trials)).map Prod.fst := by
    have law := congrArg (PMF.map (fun o : Option (Option (Finset (Edge n)) × ℕ) => (o.map Prod.fst).join))
      (EncodedSolverBits.run_fairTape (BinaryFamilySampler.choose_within cuts trials)
        (BinaryFamilySampler.choose_binary cuts trials))
    simpa only [p,q,PMF.map_comp,Function.comp_def,Option.map_map,Option.map_some,Option.join_some,draw] using law
  rw [eq]
  refine ⟨BinaryFamilySampler.choose_failure cuts (family_nonempty A w) trials,fun e => ?_⟩
  rw [BinaryFamilySampler.choose_marginal cuts (family_nonempty A w) trials (fun X => e ∈ X)]
  have nonnegative : (0 : ℝ) ≤ (cuts.countP (fun X => decide (e ∈ X)) : ℝ) / (cuts.length : ℝ) := by positivity
  exact (mul_le_of_le_one_left nonnegative (sub_le_self _ ENNReal.toReal_nonneg)).trans ((family_spec hn A w).2 e)

end DirectedFlowCutGap.RationalBudgetedRescaleEdgeFamily
