import DirectedFlowCutGap.VertexReplication
import DirectedFlowCutGap.VertexRounding

/-!
# A finite, endpoint-preserving reduction to unit vertex costs

This repairs the finite construction in Theorem 29 of arXiv:2604.03412v3.
Permanent ports, actual shortcut graphs, clipping, cost normalization, and
complete-fiber replication are composed. The final oracle is explicitly
quantified over bounded instances; no monotonicity of an exact-parameter
flow-cut-gap function is presumed. This is an existence reduction, not a
runtime bound or a proof of the main approximation theorem.
-/

namespace DirectedFlowCutGap

noncomputable section

open scoped BigOperators NNReal ENNReal

namespace UnitCostReduction

universe u
variable {V : Type u} [Fintype V] [DecidableEq V]

/-- Clip a vertex weight at the unit demand threshold. -/
def clip (w : V → ℝ≥0) (v : V) : ℝ≥0 := min 1 (w v)

/-- Clipping at one preserves every fractionally feasible demand. -/
theorem isFractionalCut_clip {G : Digraph V} {w : V → ℝ≥0}
    {D : Set (V × V)} (h : IsFractionalCut G w D) :
    IsFractionalCut G (clip w) D := by
  rw [isFractionalCut_iff] at h ⊢
  intro s t hst p
  by_cases hh : ∃ v ∈ p.internalVertices, 1 ≤ w v
  · obtain ⟨v, hv, hw⟩ := hh
    have hs : clip w v ≤ p.weight (clip w) :=
      Finset.single_le_sum (fun _ _ => zero_le) hv
    simpa only [clip, min_eq_left hw] using hs
  · have he : p.weight (clip w) = p.weight w := by
      apply Finset.sum_congr rfl
      intro v hv
      exact min_eq_right (le_of_not_ge (fun hw => hh ⟨v, hv, hw⟩))
    rw [he]
    exact h s t hst p

/-- Original cores whose total removed weight is at most one half. -/
def removed (w : V → ℝ≥0) : Finset V :=
  Finset.univ.filter fun v => w v ≤ 1 / (2 * Fintype.card V : ℝ≥0)

@[simp] theorem mem_removed (w : V → ℝ≥0) (v : V) :
    v ∈ removed w ↔ w v ≤ 1 / (2 * Fintype.card V : ℝ≥0) := by
  simp [removed]

abbrev PreparedVertex (w : V → ℝ≥0) :=
  ShortcutContraction.Survivor ((removed w).image TerminalPorts.core)

def preparedGraph (G : Digraph V) (w : V → ℝ≥0) : Digraph (PreparedVertex w) :=
  ShortcutContraction.graph (TerminalPorts.graph G) ((removed w).image TerminalPorts.core)

def preparedWeight (w : V → ℝ≥0) (v : PreparedVertex w) : ℝ≥0 :=
  min 1 (2 * TerminalPorts.extend w v.val)

def preparedCost (w c : V → ℝ≥0) (v : PreparedVertex w) : ℝ≥0 :=
  TerminalPorts.extend c v.val

def preparedDemands (w : V → ℝ≥0) (D : Set (V × V)) :
    Set (PreparedVertex w × PreparedVertex w) :=
  ShortcutContraction.portDemands (removed w) D

def pullback (w : V → ℝ≥0) (Y : Finset (PreparedVertex w)) : Finset V :=
  TerminalPorts.corePreimage (Y.image Subtype.val)

theorem prepared_fractional {G : Digraph V} {w : V → ℝ≥0}
    {D : Set (V × V)} (h : IsFractionalCut G w D) :
    IsFractionalCut (preparedGraph G w) (preparedWeight w) (preparedDemands w D) := by
  apply isFractionalCut_clip
  exact ShortcutContraction.port_isFractionalCut_double w
    (ShortcutContraction.removed_mass_le_half (removed w) w
      (fun v hv => (mem_removed w v).mp hv)) h

theorem prepared_integral_pullback {G : Digraph V} {w : V → ℝ≥0}
    {D : Set (V × V)} (Y : Finset (PreparedVertex w))
    (h : IsIntegralCut (preparedGraph G w) Y (preparedDemands w D)) :
    IsIntegralCut G (pullback w Y) D :=
  ShortcutContraction.port_isIntegralCut_pullback Y h

@[simp] theorem prepared_cutCost (w c : V → ℝ≥0) (Y : Finset (PreparedVertex w)) :
    cutCost c (pullback w Y) = cutCost (preparedCost w c) Y :=
  ShortcutContraction.port_cutCost_pullback c Y

private theorem sum_survivors_le (w : V → ℝ≥0) (f : TerminalPorts.Vertex V → ℝ≥0) :
    (∑ v : PreparedVertex w, f v.val) ≤ ∑ v, f v := by
  rw [← ShortcutContraction.sum_image_val f (Finset.univ : Finset (PreparedVertex w))]
  exact Finset.sum_le_univ_sum_of_nonneg (fun _ => zero_le)

/-- At most three representatives per original vertex survive contraction. -/
theorem prepared_card_le (w : V → ℝ≥0) :
    Fintype.card (PreparedVertex w) ≤ 3 * Fintype.card V := by
  exact (Fintype.card_subtype_le _).trans_eq TerminalPorts.card_vertex

/-- The total prepared weight is at most twice the original total. -/
theorem prepared_totalWeight_le_double (w : V → ℝ≥0) :
    totalWeight (preparedWeight w) ≤ 2 * totalWeight w := by
  calc
    _ ≤ ∑ v : PreparedVertex w, 2 * TerminalPorts.extend w v.val :=
      Finset.sum_le_sum (fun _ _ => min_le_right _ _)
    _ ≤ ∑ v : TerminalPorts.Vertex V, 2 * TerminalPorts.extend w v :=
      sum_survivors_le w (fun v => 2 * TerminalPorts.extend w v)
    _ = _ := by
      rw [← Finset.mul_sum]
      change 2 * totalWeight (TerminalPorts.extend w) = _
      rw [TerminalPorts.totalWeight_extend]

/-- Only cores have nonzero weight, so clipping bounds the total by `n`. -/
theorem prepared_totalWeight_le_card (w : V → ℝ≥0) :
    totalWeight (preparedWeight w) ≤ (Fintype.card V : ℝ≥0) := by
  calc
    _ ≤ ∑ v : PreparedVertex w, TerminalPorts.extend (fun _ => 1) v.val := by
      apply Finset.sum_le_sum
      intro v _
      rcases v with ⟨v, hv⟩
      cases v with
      | inl v => exact min_le_left _ _
      | inr v => simp [preparedWeight, TerminalPorts.extend]
    _ ≤ ∑ v : TerminalPorts.Vertex V, TerminalPorts.extend (fun _ => 1) v := sum_survivors_le w _
    _ = _ := by
      change totalWeight (TerminalPorts.extend (fun _ : V => 1)) = _
      rw [TerminalPorts.totalWeight_extend]
      simp [totalWeight]

/-- The prepared fractional cost is at most twice the original cost. -/
theorem prepared_weightedCost_le_double (w c : V → ℝ≥0) :
    weightedCost (preparedCost w c) (preparedWeight w) ≤ 2 * weightedCost c w := by
  calc
    _ ≤ ∑ v : PreparedVertex w,
        2 * (TerminalPorts.extend c v.val * TerminalPorts.extend w v.val) := by
      apply Finset.sum_le_sum
      intro v _
      dsimp [preparedCost, preparedWeight]
      calc
        _ ≤ TerminalPorts.extend c v.val * (2 * TerminalPorts.extend w v.val) :=
          mul_le_mul_of_nonneg_left (min_le_right _ _) zero_le
        _ = _ := by ring
    _ ≤ ∑ v : TerminalPorts.Vertex V,
        2 * (TerminalPorts.extend c v * TerminalPorts.extend w v) :=
      sum_survivors_le w (fun v => 2 * (TerminalPorts.extend c v * TerminalPorts.extend w v))
    _ = _ := by
      rw [← Finset.mul_sum]
      change 2 * weightedCost (TerminalPorts.extend c) (TerminalPorts.extend w) = _
      rw [TerminalPorts.weightedCost_extend]

/-- A surviving core has weight at least `1/n`; ports have zero cost.
This is the charging inequality actually needed for the copy count. -/
theorem prepared_cost_charge (w c : V → ℝ≥0) (hn : 0 < Fintype.card V)
    (v : PreparedVertex w) :
    preparedCost w c v ≤ (Fintype.card V : ℝ≥0) *
      (preparedCost w c v * preparedWeight w v) := by
  rcases v with ⟨v, hv⟩
  cases v with
  | inr v => simp [preparedCost, TerminalPorts.extend]
  | inl v =>
    have hv' : v ∉ removed w := by
      intro h
      exact hv (Finset.mem_image.mpr ⟨v, h, rfl⟩)
    have hl : 1 / (2 * Fintype.card V : ℝ≥0) < w v :=
      lt_of_not_ge (fun h => hv' ((mem_removed w v).mpr h))
    have hn' : (0 : ℝ≥0) < Fintype.card V := by exact_mod_cast hn
    have hn1 : (1 : ℝ≥0) ≤ Fintype.card V := by exact_mod_cast hn
    have hmul : (1 : ℝ≥0) < w v * (2 * Fintype.card V) :=
      (div_lt_iff₀ (mul_pos (by norm_num) hn')).mp hl
    have hweight : (1 : ℝ≥0) ≤ (Fintype.card V : ℝ≥0) * min 1 (2 * w v) := by
      rw [mul_min]
      apply le_min
      · simpa using hn1
      · nlinarith
    dsimp [preparedCost, preparedWeight, TerminalPorts.extend]
    calc
      c v = c v * 1 := (mul_one _).symm
      _ ≤ c v * ((Fintype.card V : ℝ≥0) * min 1 (2 * w v)) :=
        mul_le_mul_of_nonneg_left hweight zero_le
      _ = _ := by ring

/-- Zero fractional cost already admits a zero-cost threshold cut. -/
theorem zero_cost_cut (G : Digraph V) (w c : V → ℝ≥0)
    (h : weightedCost c w = 0) :
    ∃ X : Finset V, IsIntegralCut G X (thresholdDemands G w) ∧ cutCost c X = 0 := by
  refine ⟨vertexCardThresholdCut w, vertexCardThresholdCut_isIntegralCut G w, ?_⟩
  apply le_antisymm _ zero_le
  simpa only [h, mul_zero] using cutCost_vertexCardThresholdCut_le c w

private theorem totalWeight_pos_of_cost_pos (c w : V → ℝ≥0)
    (hc : 0 < weightedCost c w) : 0 < totalWeight w := by
  by_contra hn
  have hz : totalWeight w = 0 := le_antisymm (le_of_not_gt hn) zero_le
  have hw : ∀ v, w v = 0 := by
    intro v
    apply le_antisymm _ zero_le
    have h := Finset.single_le_sum (f := w) (fun _ _ => zero_le) (Finset.mem_univ v)
    change w v ≤ totalWeight w at h
    simpa only [hz] using h
  have he : weightedCost c w = 0 := by simp [weightedCost, hw]
  exact (ne_of_gt hc) he

/-- Every fiber is nonempty, including zero-cost permanent ports. -/
def copies (c : V → ℝ≥0) (v : V) : ℕ := max 1 ⌈c v⌉₊

theorem copies_pos (c : V → ℝ≥0) (v : V) : 1 ≤ copies c v := le_max_left _ _

theorem cost_le_copies (c : V → ℝ≥0) (v : V) : c v ≤ (copies c v : ℝ≥0) := by
  exact (Nat.le_ceil _).trans (by exact_mod_cast (le_max_right 1 ⌈c v⌉₊))

theorem copies_le_cost_add_one (c : V → ℝ≥0) (v : V) :
    (copies c v : ℝ≥0) ≤ c v + 1 := by
  rw [copies, Nat.cast_max, Nat.cast_one]
  exact max_le (by simp) (Nat.ceil_lt_add_one (show 0 ≤ c v from zero_le)).le

/-- Ceiling replication increases total weight by at most the fractional cost. -/
theorem copied_weight_le (c w : V → ℝ≥0) :
    totalWeight (VertexReplication.weight (copies c) w) ≤
      totalWeight w + weightedCost c w := by
  rw [VertexReplication.totalWeight_weight]
  calc
    _ ≤ ∑ v, (c v + 1) * w v :=
      Finset.sum_le_sum (fun v _ => mul_le_mul_of_nonneg_right (copies_le_cost_add_one c v) zero_le)
    _ = _ := by simp only [add_mul, one_mul, Finset.sum_add_distrib, totalWeight, weightedCost]; ring

/-- Ceiling replication increases cardinality by at most the sum of costs. -/
theorem copied_card_le (c : V → ℝ≥0) :
    (Fintype.card (VertexReplication.Vertex (copies c)) : ℝ≥0) ≤
      (Fintype.card V : ℝ≥0) + ∑ v, c v := by
  rw [VertexReplication.card_vertex, Nat.cast_sum]
  calc
    _ ≤ ∑ v, (c v + 1) := Finset.sum_le_sum (fun v _ => copies_le_cost_add_one c v)
    _ = _ := by simp [Finset.sum_add_distrib, add_comm]

/-- Normalize the fractional objective to one half the total weight. -/
def scale (c w : V → ℝ≥0) : ℝ≥0 :=
  totalWeight w / (2 * weightedCost c w)

def normalizedCost (c w : V → ℝ≥0) (v : V) : ℝ≥0 := scale c w * c v

@[simp] theorem weightedCost_normalizedCost (c w : V → ℝ≥0) :
    weightedCost (normalizedCost c w) w = scale c w * weightedCost c w := by
  simp only [weightedCost, normalizedCost, mul_assoc, Finset.mul_sum]

theorem scale_pos (c w : V → ℝ≥0) (hc : 0 < weightedCost c w) :
    0 < scale c w :=
  div_pos (totalWeight_pos_of_cost_pos c w hc) (mul_pos (by norm_num) hc)

theorem scale_objective (c w : V → ℝ≥0) (hc : 0 < weightedCost c w) :
    2 * (scale c w * weightedCost c w) = totalWeight w := by
  dsimp [scale]
  field_simp

/-- The actual cloned vertex type after normalization. -/
abbrev ReplicatedVertex (c w : V → ℝ≥0) :=
  VertexReplication.Vertex (copies (normalizedCost c w))

def replicatedGraph (G : Digraph V) (c w : V → ℝ≥0) : Digraph (ReplicatedVertex c w) :=
  VertexReplication.graph G (copies (normalizedCost c w))

def replicatedWeight (c w : V → ℝ≥0) : ReplicatedVertex c w → ℝ≥0 :=
  VertexReplication.weight (copies (normalizedCost c w)) w

/-- The exact finite transformed weight is bounded before using any oracle. -/
theorem normalized_copied_weight_le (c w : V → ℝ≥0) (hc : 0 < weightedCost c w) :
    totalWeight (replicatedWeight c w) ≤ 3 * (scale c w * weightedCost c w) := by
  have h := copied_weight_le (normalizedCost c w) w
  rw [weightedCost_normalizedCost] at h
  have he := scale_objective c w hc
  dsimp [replicatedWeight]
  linarith

/-- Normalization cancels on pullback, with the universal factor three. -/
theorem normalized_cutCost_pullback (c w : V → ℝ≥0)
    (hc : 0 < weightedCost c w) (α : ℝ≥0)
    (Y : Finset (ReplicatedVertex c w))
    (hY : (Y.card : ℝ≥0) ≤ α * totalWeight (replicatedWeight c w)) :
    cutCost c (VertexReplication.fullFibers Y) ≤ 3 * α * weightedCost c w := by
  have hcost := VertexReplication.cutCost_fullFibers_le_card (normalizedCost c w)
    (cost_le_copies (normalizedCost c w)) Y
  have he : cutCost (normalizedCost c w) (VertexReplication.fullFibers Y) =
      scale c w * cutCost c (VertexReplication.fullFibers Y) := by
    simp only [cutCost, normalizedCost, Finset.mul_sum]
  rw [he] at hcost
  refine le_of_mul_le_mul_left ?_ (scale_pos c w hc)
  calc
    _ ≤ (Y.card : ℝ≥0) := hcost
    _ ≤ α * totalWeight (replicatedWeight c w) := hY
    _ ≤ α * (3 * (scale c w * weightedCost c w)) :=
      mul_le_mul_of_nonneg_left (normalized_copied_weight_le c w hc) zero_le
    _ = _ := by ring

/-- Cardinality control uses the positive-core charging inequality. Zero-cost
ports contribute exactly their one mandatory copy. -/
theorem normalized_copied_card_le (c w : V → ℝ≥0) (hc : 0 < weightedCost c w)
    (n : ℕ) (hn : 0 < n) (hcard : Fintype.card V ≤ 3 * n)
    (hweight : totalWeight w ≤ (n : ℝ≥0))
    (hcharge : ∀ v, c v ≤ (n : ℝ≥0) * (c v * w v)) :
    Fintype.card (ReplicatedVertex c w) ≤ 4 * n ^ 2 := by
  have hsum : (∑ v, normalizedCost c w v) ≤
      (n : ℝ≥0) * (scale c w * weightedCost c w) := by
    calc
      _ ≤ ∑ v, (n : ℝ≥0) * ((scale c w * c v) * w v) := by
        apply Finset.sum_le_sum
        intro v _
        have h := mul_le_mul_of_nonneg_left (hcharge v) (show 0 ≤ scale c w from zero_le)
        simpa only [normalizedCost, mul_assoc, mul_left_comm, mul_comm] using h
      _ = _ := by simp only [weightedCost, Finset.mul_sum, mul_assoc]
  have hcopies := copied_card_le (normalizedCost c w)
  have hcard' : (Fintype.card V : ℝ≥0) ≤ 3 * (n : ℝ≥0) := by exact_mod_cast hcard
  have hn' : (1 : ℝ≥0) ≤ (n : ℝ≥0) := by exact_mod_cast hn
  have he := scale_objective c w hc
  have hprod : (n : ℝ≥0) * totalWeight w ≤ (n : ℝ≥0) ^ 2 := by
    simpa only [pow_two] using mul_le_mul_of_nonneg_left hweight (show (0 : ℝ≥0) ≤ n from zero_le)
  have hnorm := congrArg (fun x : ℝ≥0 => (n : ℝ≥0) * x) he
  have hnn : (n : ℝ≥0) ≤ (n : ℝ≥0) ^ 2 := by nlinarith
  have hbound : (Fintype.card (ReplicatedVertex c w) : ℝ≥0) ≤ 4 * (n : ℝ≥0) ^ 2 := by
    change (Fintype.card (VertexReplication.Vertex (copies (normalizedCost c w))) : ℝ≥0) ≤ _
    nlinarith
  exact_mod_cast hbound

/-- A unit-cost oracle with explicit bounds on the actual finite instance.
It does not identify gaps at unequal exact values of `n` or total weight. -/
def BoundedUnitRoundingOracle (N : ℕ) (B α : ℝ≥0) : Prop :=
  ∀ (U : Type u) [Fintype U] [DecidableEq U] (H : Digraph U) (z : U → ℝ≥0),
    Fintype.card U ≤ N → totalWeight z ≤ B →
    ∃ Y : Finset U, IsIntegralCut H Y (thresholdDemands H z) ∧
      (Y.card : ℝ≥0) ≤ α * totalWeight z

/-- Repaired finite Theorem 29: a unit-cost oracle on at most `4n²` vertices
and total weight at most `3W` rounds arbitrary costs within `6α`.

The original demand family may be any fractionally feasible family. Empty
vertex types and zero prepared cost are handled directly, with no division.
Every graph and cut bridge in the positive branch is the concrete port,
shortcut, clipping, and full-fiber construction above. -/
theorem round_of_bounded_unit_oracle (G : Digraph V) (w c : V → ℝ≥0)
    (D : Set (V × V)) (hf : IsFractionalCut G w D) (α : ℝ≥0)
    (oracle : BoundedUnitRoundingOracle.{u} (4 * (Fintype.card V) ^ 2)
      (3 * totalWeight w) α) :
    ∃ X : Finset V, IsIntegralCut G X D ∧ cutCost c X ≤ 6 * α * weightedCost c w := by
  classical
  by_cases hn : 0 < Fintype.card V
  · let c' := preparedCost w c
    let w' := preparedWeight w
    let H := preparedGraph G w
    have hfrac : IsFractionalCut H w' (preparedDemands w D) := prepared_fractional hf
    by_cases hc : 0 < weightedCost c' w'
    · let k := copies (normalizedCost c' w')
      let index := VertexReplication.firstIndex k (copies_pos (normalizedCost c' w'))
      have hcard : Fintype.card (ReplicatedVertex c' w') ≤ 4 * (Fintype.card V) ^ 2 :=
        normalized_copied_card_le c' w' hc (Fintype.card V) hn (prepared_card_le w)
          (prepared_totalWeight_le_card w) (prepared_cost_charge w c hn)
      have hweight : totalWeight (replicatedWeight c' w') ≤ 3 * totalWeight w := by
        have hb := normalized_copied_weight_le c' w' hc
        have he := scale_objective c' w' hc
        have hw := prepared_totalWeight_le_double w
        change totalWeight w' ≤ 2 * totalWeight w at hw
        nlinarith
      obtain ⟨Y, hY, hsize⟩ := oracle (ReplicatedVertex c' w') (replicatedGraph H c' w')
        (replicatedWeight c' w') hcard hweight
      have hf' : IsFractionalCut (replicatedGraph H c' w') (replicatedWeight c' w')
          (VertexReplication.demands index (preparedDemands w D)) :=
        (VertexReplication.isFractionalCut_iff index w' (preparedDemands w D)).mpr hfrac
      have hi : IsIntegralCut H (VertexReplication.fullFibers Y) (preparedDemands w D) := by
        apply VertexReplication.isIntegralCut_pullback index Y
        intro s t hst
        exact hY s t (hf' s t hst)
      refine ⟨pullback w (VertexReplication.fullFibers Y), prepared_integral_pullback _ hi, ?_⟩
      rw [prepared_cutCost]
      have hb := normalized_cutCost_pullback c' w' hc α Y hsize
      have hC := prepared_weightedCost_le_double w c
      change weightedCost c' w' ≤ 2 * weightedCost c w at hC
      calc
        _ ≤ 3 * α * weightedCost c' w' := hb
        _ ≤ 3 * α * (2 * weightedCost c w) := mul_le_mul_of_nonneg_left hC zero_le
        _ = _ := by ring
    · have hz : weightedCost c' w' = 0 := le_antisymm (le_of_not_gt hc) zero_le
      obtain ⟨Y, hY, hcost⟩ := zero_cost_cut H w' c' hz
      have hi : IsIntegralCut H Y (preparedDemands w D) := fun s t hst => hY s t (hfrac s t hst)
      refine ⟨pullback w Y, prepared_integral_pullback _ hi, ?_⟩
      rw [prepared_cutCost]
      change cutCost c' Y ≤ _
      rw [hcost]
      exact zero_le
  · haveI : IsEmpty V := Fintype.card_eq_zero_iff.mp (Nat.eq_zero_of_not_pos hn)
    refine ⟨∅, ?_, ?_⟩
    · intro s
      exact isEmptyElim s
    · simp [cutCost]

/-- Specialization to the original all-pairs threshold-cut problem. -/
theorem threshold_round_of_bounded_unit_oracle (G : Digraph V) (w c : V → ℝ≥0)
    (α : ℝ≥0) (oracle : BoundedUnitRoundingOracle.{u} (4 * (Fintype.card V) ^ 2)
      (3 * totalWeight w) α) :
    ∃ X : Finset V, IsIntegralCut G X (thresholdDemands G w) ∧
      cutCost c X ≤ 6 * α * weightedCost c w :=
  round_of_bounded_unit_oracle G w c (thresholdDemands G w)
    (isFractionalCut_thresholdDemands G w) α oracle

/-- The repaired reduction plugs directly into the existing vertex-rounding
interface, keeping its bounded unit-cost oracle as an explicit hypothesis. -/
theorem hasVertexRoundingFactor_of_bounded_unit_oracle (G : Digraph V) (w : V → ℝ≥0)
    (α : ℝ≥0) (oracle : BoundedUnitRoundingOracle.{u} (4 * (Fintype.card V) ^ 2)
      (3 * totalWeight w) α) :
    HasVertexRoundingFactor G w (6 * (α : ℝ)) := by
  refine ⟨by positivity, ?_⟩
  intro c
  obtain ⟨X, hX, hcost⟩ := threshold_round_of_bounded_unit_oracle G w c α oracle
  refine ⟨X, hX, ?_⟩
  exact_mod_cast hcost

end UnitCostReduction
end
end DirectedFlowCutGap
