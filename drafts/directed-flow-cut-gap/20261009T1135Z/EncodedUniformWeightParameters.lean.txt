import DirectedFlowCutGap.EncodedPortPreparation
import DirectedFlowCutGap.UniformWeightReduction

/-!
# Rational parameters for the bounded uniform-weight chain reduction

Clipped original cores and permanent zero-weight ports are encoded in three
consecutive blocks. The raw average and each chain multiplicity are evaluated
once. A low clipped-total branch permits the empty original cut, including
unreachable demands and empty inputs. The nontrivial branch has total at least
one, which bounds the eventual integer cutoff by the original port count.

This file prices natural arithmetic in the declared word model. Counter
bookkeeping is ghost instrumentation; actual stored numerator/denominator
widths are stated separately.
-/

namespace DirectedFlowCutGap.EncodedUniformWeightParameters

open scoped BigOperators NNReal NNRat
open RawNonnegativeRational EncodedUnitCostReplication EncodedPortPreparation

def portWeight {n : ℕ} (D : Input n) : Port n → Code
  | .inl v => clipOne D.weights[v.val]
  | .inr _ => Code.zero

def portInput {n : ℕ} (D : Input n) : Input (3*n) :=
  let m := 3*n
  { adjacency := Vector.ofFn (n := m) fun i => Vector.ofFn (n := m) fun j =>
      portAdj D (decodePort i) (decodePort j)
    weights := Vector.ofFn (n := m) fun i => portWeight D (decodePort i)
    costs := Vector.replicate m Code.one }

theorem port_graph {n : ℕ} (D : Input n) (i j : Fin (3*n)) :
    (portInput D).graph.Adj i j ↔
      (TerminalPorts.graph D.graph).Adj (decodePort i) (decodePort j) := by
  simpa [Input.graph,portInput] using portAdj_refines D (decodePort i) (decodePort j)

theorem port_weight {n : ℕ} (D : Input n) (i : Fin (3*n)) :
    (portInput D).weight i = UniformWeightReduction.preparedWeight D.weight (decodePort i) := by
  simp only [Input.weight,portInput,Vector.getElem_ofFn]
  cases decodePort i <;>
    simp [portWeight,UniformWeightReduction.preparedWeight,TerminalPorts.extend,
      UnitCostReduction.clip,Code.realValue,NNRat.cast_min,Input.weight]

theorem port_totalWeight {n : ℕ} (D : Input n) :
    totalWeight (portInput D).weight =
      totalWeight (UniformWeightReduction.preparedWeight D.weight) := by
  simp only [totalWeight,port_weight]
  exact (portEquiv n).sum_comp _

theorem port_totalWeight_clip {n : ℕ} (D : Input n) :
    totalWeight (portInput D).weight = totalWeight (UnitCostReduction.clip D.weight) := by
  rw [port_totalWeight,UniformWeightReduction.preparedWeight,TerminalPorts.totalWeight_extend]

/-- No existing path can be a threshold demand if the total clipped mass is
below one. Unreachable pairs remain cut by the empty set. -/
theorem empty_cut_of_small_total {n : ℕ} (D : Input n)
    (h : totalWeight (portInput D).weight < 1) :
    IsIntegralCut D.graph ∅ (thresholdDemands D.graph D.weight) := by
  have hf := UnitCostReduction.isFractionalCut_clip (isFractionalCut_thresholdDemands D.graph D.weight)
  rw [isFractionalCut_iff] at hf
  intro s t hst p
  have hp := hf s t hst p
  have hb : p.weight (UnitCostReduction.clip D.weight) ≤
      totalWeight (UnitCostReduction.clip D.weight) :=
    Finset.sum_le_univ_sum_of_nonneg (fun _ => zero_le)
  rw [← port_totalWeight_clip D] at hb
  exact ((not_le_of_gt h) (hp.trans hb)).elim

structure Parameters (n : ℕ) where
  ports : Input (3*n)
  total : Code
  average : Code
  ratios : Vector Code (3*n)
  counts : Vector ℕ (3*n)
  work : ℕ

/-- The 80 operations per graph cell cover both port decodes, bounded input
reads and all array-loop callbacks/pushes/wrappers. The linear allowances pay
clipping, unit costs, enumeration, retained average, ratio and ceiling arrays.
No loop has a length equal to a rational numerator or denominator. -/
def compute {n : ℕ} (D : Input n) : Parameters n :=
  let m := 3*n
  let P := portInput D
  let T := P.totals
  let avg := T.weight.div (Code.ofNat m)
  let ratios := Vector.ofFn (n := m) fun i => P.weights[i.val].div avg
  let counts := Input.copyCounts ratios
  { ports := P, total := T.weight, average := avg, ratios := ratios, counts := counts
    work := 80*m^2+80*m+20+T.work+80*m+30 }

@[simp] theorem compute_total {n : ℕ} (D : Input n) :
    (compute D).total.realValue = totalWeight (UniformWeightReduction.preparedWeight D.weight) := by
  change (portInput D).totals.weight.realValue = _
  rw [Input.totals_weight,port_totalWeight]

@[simp] theorem compute_average {n : ℕ} (D : Input n) :
    (compute D).average.realValue =
      UniformWeightReduction.average (UniformWeightReduction.preparedWeight D.weight) := by
  simp only [compute,Code.realValue,Code.value_div,Code.value_ofNat,NNRat.cast_div,
    NNRat.cast_natCast,UniformWeightReduction.average,TerminalPorts.card_vertex,Fintype.card_fin]
  change (portInput D).totals.weight.realValue / (3*n : ℕ) = _
  rw [Input.totals_weight,port_totalWeight]

@[simp] theorem compute_ratios {n : ℕ} (D : Input n) (i : Fin (3*n)) :
    (compute D).ratios[i.val].realValue =
      UniformWeightReduction.preparedWeight D.weight (decodePort i) /
        UniformWeightReduction.average (UniformWeightReduction.preparedWeight D.weight) := by
  have h : (compute D).ratios[i.val].realValue =
      (portInput D).weight i / (compute D).average.realValue := by
    simp [compute,Code.realValue,Input.weight]
  rw [h,port_weight,compute_average]

theorem compute_counts {n : ℕ} (D : Input n) (i : Fin (3*n)) :
    (compute D).counts[i.val] =
      UniformWeightReduction.copies (UniformWeightReduction.preparedWeight D.weight) (decodePort i) := by
  have hc : (compute D).counts[i.val] = max 1 ((compute D).ratios[i.val].ceil) := by
    simp [compute,Input.copyCounts]
  rw [hc]
  rw [Code.ceil_eq,UniformWeightReduction.copies,← compute_ratios D i]
  simp [Code.realValue]

theorem counts_positive {n : ℕ} (D : Input n) (i : Fin (3*n)) :
    0 < (compute D).counts[i.val] := by
  rw [compute_counts]
  exact UniformWeightReduction.copies_pos _ _

noncomputable def cloneEquiv {n : ℕ} (D : Input n) :
    Clone (compute D).counts ≃ UniformWeightReduction.ExpandedVertex D.weight :=
  Equiv.sigmaCongr (portEquiv n) (fun i => finCongr (compute_counts D i))

@[simp] theorem cloneEquiv_fst {n : ℕ} (D : Input n) (a : Clone (compute D).counts) :
    (cloneEquiv D a).1 = decodePort a.1 := rfl

@[simp] theorem cloneEquiv_snd_val {n : ℕ} (D : Input n) (a : Clone (compute D).counts) :
    (cloneEquiv D a).2.val = a.2.val := rfl

theorem clone_count {n : ℕ} (D : Input n)
    (h : 0 < (compute D).total.realValue) :
    (cloneList (compute D).counts).length ≤ 6*n := by
  rw [cloneList_length,Fintype.card_congr (cloneEquiv D)]
  simpa using UniformWeightReduction.expanded_card_le D.weight (by simpa using h)

theorem port_count_le_clones {n : ℕ} (D : Input n) :
    3*n ≤ (cloneList (compute D).counts).length := by
  rw [cloneList_length,Fintype.card_sigma]
  simp only [Fintype.card_fin]
  calc
    3*n = ∑ _i : Fin (3*n), 1 := by simp
    _ ≤ ∑ i : Fin (3*n), (compute D).counts[i.val] :=
      Finset.sum_le_sum (fun i _ => counts_positive D i)

theorem compute_work {n : ℕ} (D : Input n) :
    (compute D).work = 720*n^2+567*n+51 := by
  simp only [compute,Input.totals_work]
  ring

theorem port_weights_bounded {n : ℕ} (D : Input n) (b : ℕ)
    (h : ∀ i : Fin n, D.weights[i.val].Bounded b) (i : Fin (3*n)) :
    (portInput D).weights[i.val].Bounded b := by
  simp only [portInput,Vector.getElem_ofFn]
  cases decodePort i with
  | inl v => exact clipOne_bounded (h v)
  | inr p => exact Code.bounded_mono Code.bounded_zero (Nat.zero_le _)

theorem total_bounded {n : ℕ} (D : Input n) (b : ℕ)
    (h : ∀ i : Fin n, D.weights[i.val].Bounded b) :
    (compute D).total.Bounded (3*n*(b+1)) := by
  have hh := (portInput D).scan_bounded b (port_weights_bounded D b h)
    (fun i => by simpa [portInput] using Code.bounded_mono Code.bounded_one (Nat.zero_le b))
    (List.finRange (3*n))
  simpa only [compute,Input.totals,List.length_finRange] using hh.1

theorem average_bounded {n : ℕ} (D : Input n) (b : ℕ)
    (h : ∀ i : Fin n, D.weights[i.val].Bounded b) :
    (compute D).average.Bounded (3*n*(b+1)+Nat.size (3*n)) := by
  exact Code.bounded_div (total_bounded D b h)
    ⟨(Nat.lt_size_self _).le,Nat.one_le_two_pow⟩

theorem ratios_bounded {n : ℕ} (D : Input n) (b : ℕ)
    (h : ∀ i : Fin n, D.weights[i.val].Bounded b) (i : Fin (3*n)) :
    (compute D).ratios[i.val].Bounded (b+(3*n*(b+1)+Nat.size (3*n))) := by
  have hh := Code.bounded_div (port_weights_bounded D b h i) (average_bounded D b h)
  simpa only [compute,Vector.getElem_ofFn] using hh

def nontrivial {n : ℕ} (D : Input n) : Bool := Code.one.le (compute D).total

theorem nontrivial_iff {n : ℕ} (D : Input n) :
    nontrivial D = true ↔ 1 ≤ totalWeight (UniformWeightReduction.preparedWeight D.weight) := by
  rw [← compute_total]
  simp [nontrivial,Code.realValue]

theorem trivial_cut {n : ℕ} (D : Input n) (h : nontrivial D ≠ true) :
    IsIntegralCut D.graph ∅ (thresholdDemands D.graph D.weight) := by
  apply empty_cut_of_small_total
  rw [port_totalWeight]
  exact lt_of_not_ge (fun hh => h ((nontrivial_iff D).mpr hh))

def cutoff {n : ℕ} (D : Input n) : ℕ := (Code.one.div (compute D).average).ceil

theorem cutoff_eq {n : ℕ} (D : Input n) :
    cutoff D = ⌈1 / UniformWeightReduction.average
      (UniformWeightReduction.preparedWeight D.weight)⌉₊ := by
  rw [cutoff,Code.ceil_eq,← compute_average]
  simp only [Code.realValue,Code.value_div,Code.value_one,one_div]
  rw [← NNRat.cast_inv,NNRat.ceil_cast]

theorem cutoff_positive {n : ℕ} (D : Input n) (h : nontrivial D = true) : 0 < cutoff D := by
  have hW := (nontrivial_iff D).mp h
  have ha := UniformWeightReduction.average_pos _ (lt_of_lt_of_le (by norm_num) hW)
  rw [cutoff_eq]
  exact Nat.ceil_pos.mpr (div_pos (by norm_num) ha)

/-- The branch is tested before the integer core allocates cutoff-dependent
state. The finite threshold is bounded by the port count, hence by the actual
chain output size, independently of the numerical input denominators. -/
theorem cutoff_le_ports {n : ℕ} (D : Input n) (h : nontrivial D = true) : cutoff D ≤ 3*n := by
  have hW := (nontrivial_iff D).mp h
  have hWp : 0 < totalWeight (UniformWeightReduction.preparedWeight D.weight) :=
    lt_of_lt_of_le (by norm_num) hW
  rw [cutoff_eq,Nat.ceil_le]
  simp only [UniformWeightReduction.average,one_div_div,TerminalPorts.card_vertex,Fintype.card_fin]
  apply (div_le_iff₀ hWp).mpr
  simpa using mul_le_mul_of_nonneg_left hW (show 0 ≤ (3*n : ℝ≥0) from zero_le)

theorem cutoff_le_clones {n : ℕ} (D : Input n) (h : nontrivial D = true) :
    cutoff D ≤ (cloneList (compute D).counts).length :=
  (cutoff_le_ports D h).trans (port_count_le_clones D)

/-- Converting to an integer cutoff can only decrease the reciprocal scale
used by the integer core's size estimate. -/
theorem reciprocal_cutoff_le_average {n : ℕ} (D : Input n) (h : nontrivial D = true) :
    (1 : ℝ≥0)/(cutoff D : ℝ≥0) ≤ (compute D).average.realValue := by
  have hW := (nontrivial_iff D).mp h
  have ha : 0 < (compute D).average.realValue := by
    rw [compute_average]
    exact UniformWeightReduction.average_pos _ (lt_of_lt_of_le (by norm_num) hW)
  have hL : (0 : ℝ≥0) < cutoff D := by exact_mod_cast cutoff_positive D h
  have hc : 1/(compute D).average.realValue ≤ (cutoff D : ℝ≥0) := by
    rw [cutoff_eq,compute_average]
    exact Nat.le_ceil _
  apply (div_le_iff₀ hL).mpr
  simpa only [mul_comm] using (div_le_iff₀ ha).mp hc

theorem cutoff_operand_bits {n : ℕ} (D : Input n) (b : ℕ)
    (h : ∀ i : Fin n, D.weights[i.val].Bounded b) :
    let q := Code.one.div (compute D).average
    Nat.size q.num ≤ 3*n*(b+1)+Nat.size (3*n)+1 ∧
      Nat.size q.den ≤ 3*n*(b+1)+Nat.size (3*n)+1 := by
  simpa using Code.bounded_bits (Code.bounded_div Code.bounded_one (average_bounded D b h))

end DirectedFlowCutGap.EncodedUniformWeightParameters
