import DirectedFlowCutGap.RationalDerivedEdgeFamily

/-! Compute the original-weight rational family at the positive arc count.
The computed instance factor is bounded by the exact original paper factor. -/
namespace DirectedFlowCutGap.RationalPositiveArcEdgeFamily

open scoped BigOperators NNReal NNRat
open BinaryFractionalWalkOracle (Adjacency graph)
open RationalEdgeThresholds (Weights weights)
open RationalEdgeDecomposition (Good originalWeight originalWeight_eq)
open RationalExactEdgeOracle (Edge)
open RationalOriginalEdgeFamily (light lightMass floor build horizon adaptive)
open RationalDerivedEdgeFamily (factor factor_valid)

variable {n : ℕ}

def positiveArcs (A : Adjacency n) (w : Weights n) : Finset (Edge n) :=
  Finset.univ.filter fun e => 0 < originalWeight A w e

theorem positiveArcs_mem (A : Adjacency n) (w : Weights n) (e : Edge n) :
    e ∈ positiveArcs A w ↔ e ∈ graphEdges (graph A) ∧ 0 < weights w e := by
  have positive : 0 < originalWeight A w e ↔ 0 < actualEdgeWeight (graph A) (weights w) e := by
    rw [← originalWeight_eq,← NNRat.cast_zero (α := ℝ≥0),NNRat.cast_lt]
  simp only [positiveArcs,Finset.mem_filter,Finset.mem_univ,true_and,positive]
  by_cases arc : (graph A).Adj e.1 e.2
  · rw [actualEdgeWeight_of_adj _ _ arc]
    simp only [(mem_graphEdges _ _).mpr arc,true_and]
  · rw [actualEdgeWeight_of_not_adj _ _ arc]
    simp only [lt_self_iff_false,mem_graphEdges,arc,false_and]

def count (A : Adjacency n) (w : Weights n) : ℕ := max 1 (positiveArcs A w).card

theorem count_positive (A : Adjacency n) (w : Weights n) : 0 < count A w :=
  Nat.zero_lt_one.trans_le (le_max_left _ _)

theorem small_mass (A : Adjacency n) (w : Weights n) (α : ℚ≥0) (pos : 0 < α) :
    lightMass A w α (count A w) ≤ 1/4 := by
  let k := count A w
  let δ := floor k α
  let S := light A w α k
  let P := positiveArcs A w
  have keep : (∑ e ∈ S ∩ P,originalWeight A w e) = ∑ e ∈ S,originalWeight A w e := by
    apply Finset.sum_subset Finset.inter_subset_left
    intro e lit absent
    have nonpos : ¬ 0 < originalWeight A w e := fun high =>
      absent (Finset.mem_inter.mpr ⟨lit,Finset.mem_filter.mpr ⟨Finset.mem_univ _,high⟩⟩)
    exact le_antisymm (le_of_not_gt nonpos) zero_le
  have bound : (∑ e ∈ S,originalWeight A w e) ≤ (k : ℚ≥0)*δ := by
    rw [← keep]
    calc
      _ ≤ ∑ _e ∈ S ∩ P, δ := Finset.sum_le_sum fun e hit =>
        (Finset.mem_filter.mp (Finset.mem_inter.mp hit).1).2.le
      _ = ((S ∩ P).card : ℚ≥0)*δ := by simp [nsmul_eq_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (Nat.cast_le.mpr ((Finset.card_le_card Finset.inter_subset_right).trans (le_max_right _ _))) zero_le
  change α * (∑ e ∈ S,originalWeight A w e) ≤ _
  refine (mul_le_mul_of_nonneg_left bound pos.le).trans_eq ?_
  unfold δ floor
  have kpos : (k : ℚ≥0) ≠ 0 := Nat.cast_ne_zero.mpr (count_positive A w).ne'
  field_simp [pos.ne',kpos]

def family (A : Adjacency n) (w : Weights n) : RationalWeakFamily.History (Edge n) :=
  let α := factor A w
  if α = 0 then adaptive A w α else build A w α (count A w)

theorem family_length (A : Adjacency n) (w : Weights n) :
    (family A w).cuts.length = if factor A w = 0 then 1 else horizon A w (factor A w) (count A w) := by
  by_cases zero : factor A w = 0
  · simp [family,zero,adaptive]
  · simp only [family,ite_eq_right zero,RationalOriginalEdgeFamily.build_length]

theorem family_nonempty (A : Adjacency n) (w : Weights n) : 0 < (family A w).cuts.length := by
  rw [family_length]
  split
  · exact Nat.zero_lt_one
  · exact RationalWeakFamily.edgeRounds_pos _ _

theorem length_le_original_factor (A : Adjacency n) (w : Weights n) :
    let α := ExactFlowCutGap.efg n (totalEdgeWeight (graph A) (weights w))
    (family A w).cuts.length ≤ horizon A w (α : ℚ≥0) (count A w) := by
  let α : ℚ≥0 := (ExactFlowCutGap.efg n (totalEdgeWeight (graph A) (weights w)) : ℕ)
  have smaller : factor A w ≤ α := Nat.cast_le.mpr (RationalInstanceEdgeFactor.least_le_original_factor A w)
  change (family A w).cuts.length ≤ horizon A w α (count A w)
  rw [family_length]
  split
  · exact RationalWeakFamily.edgeRounds_pos _ _
  · unfold horizon RationalWeakFamily.edgeRounds RationalWeakFamily.edgeMagnitude
    apply Nat.add_le_add_right
    apply Nat.mul_le_mul_left
    apply Nat.size_le_size
    apply Nat.ceil_mono
    gcongr

private theorem loss_le (A : Adjacency n) (w : Weights n) (e : Edge n) :
    8*(originalWeight A w e : ℝ)*(factor A w : ℝ) ≤
      8*(originalWeight A w e : ℝ)*(ExactFlowCutGap.efg n (totalEdgeWeight (graph A) (weights w)) : ℝ) := by
  simp only [factor,NNRat.cast_natCast]
  exact mul_le_mul_of_nonneg_left
    (Nat.cast_le.mpr (RationalInstanceEdgeFactor.least_le_original_factor A w))
    (mul_nonneg (by norm_num) (NNRat.cast_nonneg _))

theorem family_spec (A : Adjacency n) (w : Weights n) :
    let L := (family A w).cuts
    (∀ X ∈ L, Good A w X) ∧
      ∀ e, (L.countP (fun X => decide (e ∈ X)) : ℝ)/(L.length : ℝ) ≤
        8*(originalWeight A w e : ℝ)*(ExactFlowCutGap.efg n (totalEdgeWeight (graph A) (weights w)) : ℝ) := by
  by_cases hn : 0 < n
  · by_cases zero : factor A w = 0
    · have same := RationalOriginalEdgeFamily.adaptive_spec_all hn A w _ (factor_valid A w)
      simpa only [family,ite_eq_left zero] using ⟨same.1,fun e => (same.2 e).trans (loss_le A w e)⟩
    · have pos : 0 < factor A w := lt_of_le_of_ne zero_le (Ne.symm zero)
      have spec := RationalOriginalEdgeFamily.build_spec A w _ (count_positive A w) pos
        (small_mass A w _ pos) (factor_valid A w)
      simpa only [family,ite_eq_right zero] using ⟨fun X h => (spec.1 X h).1,
        fun e => (spec.2 e).trans (loss_le A w e)⟩
  · have empty : n=0 := by omega
    subst n
    exact ⟨fun X _ => ⟨fun e _ => Fin.elim0 e.1,fun s => Fin.elim0 s⟩,fun e => Fin.elim0 e.1⟩

def draw (A : Adjacency n) (w : Weights n) (trials : ℕ) (tape : List Bool) :
    Option ((Option (Finset (Edge n)) × ℕ) × EncodedSolverBits.Tape) :=
  EncodedSolverBits.run (BinaryFamilySampler.choose (family A w).cuts trials) tape

theorem draw_used (A : Adjacency n) (w : Weights n) (trials : ℕ) (tape : List Bool)
    (enough : trials*FairBitWords.width (family A w).cuts.length ≤ tape.length) :
    ∃ cut paid used, draw A w trials tape = some ((cut,paid),(tape.drop used,used)) ∧
      used ≤ trials*FairBitWords.width (family A w).cuts.length :=
  BinaryFamilySampler.choose_used _ _ _ enough

theorem draw_valid (A : Adjacency n) (w : Weights n) {trials : ℕ} {tape rest : List Bool}
    {cut : Finset (Edge n)} {paid used : ℕ}
    (played : draw A w trials tape = some ((some cut,paid),(rest,used))) : Good A w cut := by
  let L := (family A w).cuts
  have seen := EncodedSolverBits.run_support (BinaryFamilySampler.choose_binary L trials) played
  have inList := (BinaryFamilySampler.choose_supported L trials seen).1 cut (by simp)
  exact (family_spec A w).1 cut inList

theorem draw_law (A : Adjacency n) (w : Weights n) (trials : ℕ) :
    let L := (family A w).cuts
    let q := trials*FairBitWords.width L.length
    let p := (EncodedSolverBits.fairTape q).map (fun tape => ((draw A w trials tape).map (fun r => r.1.1)).join)
    p none = BoundedBitRejection.law L.length trials none ∧
      ∀ e, FiniteAmplification.probability p (fun o => ∃ X ∈ o, e ∈ X) ≤
        8*(originalWeight A w e : ℝ)*(ExactFlowCutGap.efg n (totalEdgeWeight (graph A) (weights w)) : ℝ) := by
  let L := (family A w).cuts
  let q := trials*FairBitWords.width L.length
  let p := (EncodedSolverBits.fairTape q).map (fun tape => ((draw A w trials tape).map (fun r => r.1.1)).join)
  change p none = _ ∧ ∀ e, FiniteAmplification.probability p (fun o => ∃ X ∈ o, e ∈ X) ≤ _
  have eq : p = (FiniteDrawTrees.ideal (BinaryFamilySampler.choose L trials)).map Prod.fst := by
    have h := congrArg (PMF.map (fun o : Option (Option (Finset (Edge n)) × ℕ) => (o.map Prod.fst).join))
      (EncodedSolverBits.run_fairTape (BinaryFamilySampler.choose_within L trials)
        (BinaryFamilySampler.choose_binary L trials))
    simpa only [p,q,PMF.map_comp,Function.comp_def,Option.map_map,Option.map_some,Option.join_some,draw] using h
  rw [eq]
  refine ⟨BinaryFamilySampler.choose_failure L (family_nonempty A w) trials,fun e => ?_⟩
  rw [BinaryFamilySampler.choose_marginal L (family_nonempty A w) trials (fun X => e ∈ X)]
  have nonnegative : (0 : ℝ) ≤ (L.countP (fun X => decide (e ∈ X)) : ℝ)/(L.length : ℝ) := by positivity
  exact (mul_le_of_le_one_left nonnegative (sub_le_self _ ENNReal.toReal_nonneg)).trans ((family_spec A w).2 e)

end DirectedFlowCutGap.RationalPositiveArcEdgeFamily
