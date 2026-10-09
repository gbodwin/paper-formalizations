import DirectedFlowCutGap.VertexRounding

/-!
# Finite heavy-vertex self-reduction

The finite graph construction underlying Theorem 32 of arXiv:2604.03412v3,
`tex/reductions.tex:627–681`. For `0 < τ ≤ 1/4`, delete vertices of weight
at least `τ`, double the remaining weights, round the actual residual graph,
and adjoin the heavy vertices. Original demand endpoints need not survive.
The proof instead trims an original avoiding path to its first and last
internal vertices and proves that these form a residual threshold demand.

The heavy cost is `C/τ`, correcting the source's displayed reciprocal typo.
The oracle is quantified over explicitly bounded instances; there is no
assumption that an exact-parameter gap function is monotone. These are finite
existence results, with no algorithmic runtime or asymptotic claim.
-/

namespace DirectedFlowCutGap

noncomputable section

open scoped BigOperators NNReal ENNReal

namespace WeightSelfReduction

universe u
variable {V : Type u} [Fintype V] [DecidableEq V]

/-- The first part of the final cut. -/
def heavy (w : V → ℝ≥0) (τ : ℝ≥0) : Finset V :=
  Finset.univ.filter fun v => τ ≤ w v

omit [DecidableEq V] in
@[simp] theorem mem_heavy (w : V → ℝ≥0) (τ : ℝ≥0) (v : V) :
    v ∈ heavy w τ ↔ τ ≤ w v := by simp [heavy]

/-- The residual instance has an actual restricted vertex type. -/
abbrev Residual (w : V → ℝ≥0) (τ : ℝ≥0) := {v : V // v ∉ heavy w τ}

def graph (G : Digraph V) (w : V → ℝ≥0) (τ : ℝ≥0) : Digraph (Residual w τ) where
  Adj a b := G.Adj a.val b.val

def weight (w : V → ℝ≥0) (τ : ℝ≥0) (v : Residual w τ) : ℝ≥0 := 2 * w v.val

def cost (w c : V → ℝ≥0) (τ : ℝ≥0) (v : Residual w τ) : ℝ≥0 := c v.val

def liftCut {w : V → ℝ≥0} {τ : ℝ≥0} (Y : Finset (Residual w τ)) : Finset V :=
  Y.image Subtype.val

def combinedCut (w : V → ℝ≥0) (τ : ℝ≥0) (Y : Finset (Residual w τ)) : Finset V :=
  heavy w τ ∪ liftCut Y

omit [DecidableEq V] in
theorem survivor_weight_lt {w : V → ℝ≥0} {τ : ℝ≥0} (v : Residual w τ) :
    w v.val < τ := lt_of_not_ge (fun h => v.property ((mem_heavy w τ v.val).mpr h))

theorem residual_card_le (w : V → ℝ≥0) (τ : ℝ≥0) :
    Fintype.card (Residual w τ) ≤ Fintype.card V := Fintype.card_subtype_le _

theorem sum_liftCut (f : V → ℝ≥0) {w : V → ℝ≥0} {τ : ℝ≥0}
    (Y : Finset (Residual w τ)) :
    (∑ v ∈ liftCut Y, f v) = ∑ v ∈ Y, f v.val := by
  rw [liftCut, Finset.sum_image]
  intro a _ b _ h
  exact Subtype.ext h

theorem sum_residual_le (f : V → ℝ≥0) (w : V → ℝ≥0) (τ : ℝ≥0) :
    (∑ v : Residual w τ, f v.val) ≤ ∑ v, f v := by
  rw [← sum_liftCut f (Finset.univ : Finset (Residual w τ))]
  exact Finset.sum_le_univ_sum_of_nonneg (fun _ => zero_le)

/-- Every surviving weight is below `τ`; no positive cardinality is needed. -/
theorem residual_totalWeight_le (w : V → ℝ≥0) (τ : ℝ≥0) :
    totalWeight (weight w τ) ≤ 2 * (Fintype.card V : ℝ≥0) * τ := by
  calc
    _ ≤ ∑ _v : Residual w τ, 2 * τ :=
      Finset.sum_le_sum (fun v _ => mul_le_mul_of_nonneg_left (survivor_weight_lt v).le zero_le)
    _ = (Fintype.card (Residual w τ) : ℝ≥0) * (2 * τ) := by simp
    _ ≤ (Fintype.card V : ℝ≥0) * (2 * τ) := by
      apply mul_le_mul_of_nonneg_right _ zero_le
      exact_mod_cast residual_card_le w τ
    _ = _ := by ring

/-- Deletion never increases the objective before the explicit doubling. -/
theorem residual_weightedCost_le (w c : V → ℝ≥0) (τ : ℝ≥0) :
    weightedCost (cost w c τ) (weight w τ) ≤ 2 * weightedCost c w := by
  calc
    _ = ∑ v : Residual w τ, 2 * (c v.val * w v.val) := by
      apply Finset.sum_congr rfl
      intro v _
      dsimp [cost, weight]
      ring
    _ ≤ ∑ v, 2 * (c v * w v) := sum_residual_le (fun v => 2 * (c v * w v)) w τ
    _ = _ := by simp only [weightedCost, Finset.mul_sum]

omit [DecidableEq V] in
/-- This is the reciprocal factor `1/τ`, rather than the source's typo. -/
theorem heavy_cutCost_le (w c : V → ℝ≥0) (τ : ℝ≥0) (hτ : 0 < τ) :
    cutCost c (heavy w τ) ≤ weightedCost c w / τ := by
  apply (le_div_iff₀ hτ).mpr
  calc
    _ = ∑ v ∈ heavy w τ, c v * τ := by rw [cutCost, Finset.sum_mul]
    _ ≤ ∑ v ∈ heavy w τ, c v * w v := by
      apply Finset.sum_le_sum
      intro v hv
      exact mul_le_mul_of_nonneg_left ((mem_heavy w τ v).mp hv) zero_le
    _ ≤ weightedCost c w := Finset.sum_le_univ_sum_of_nonneg (fun _ => zero_le)

@[simp] theorem cutCost_liftCut (w c : V → ℝ≥0) (τ : ℝ≥0)
    (Y : Finset (Residual w τ)) : cutCost c (liftCut Y) = cutCost (cost w c τ) Y :=
  sum_liftCut c Y

theorem heavy_disjoint_liftCut (w : V → ℝ≥0) (τ : ℝ≥0)
    (Y : Finset (Residual w τ)) : Disjoint (heavy w τ) (liftCut Y) := by
  apply Finset.disjoint_left.mpr
  intro v hv hY
  obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hY
  exact a.property hv

theorem combined_cutCost (w c : V → ℝ≥0) (τ : ℝ≥0)
    (Y : Finset (Residual w τ)) :
    cutCost c (combinedCut w τ Y) = cutCost c (heavy w τ) + cutCost (cost w c τ) Y := by
  rw [combinedCut, cutCost, Finset.sum_union (heavy_disjoint_liftCut w τ Y)]
  exact congrArg (fun x => cutCost c (heavy w τ) + x) (cutCost_liftCut w c τ Y)

namespace Path

variable {G : Digraph V} {s t : V}

omit [Fintype V] in
/-- Strictly interior indices really are internal vertices, by simplicity. -/
theorem index_internal (p : SimplePath G s t) (i : Fin (p.edgeLength + 1))
    (hi : 0 < i.val) (hj : i.val < p.edgeLength) : p.vertex i ∈ p.internalVertices := by
  apply (p.mem_internalVertices _).mpr
  refine ⟨⟨i, rfl⟩, ?_, ?_⟩
  · intro h
    have he := congrArg Fin.val (p.injective (h.trans p.source_eq.symm))
    change i.val = 0 at he
    omega
  · intro h
    have he := congrArg Fin.val (p.injective (h.trans p.target_eq.symm))
    change i.val = p.edgeLength at he
    omega

omit [Fintype V] in
/-- A positive-weight path has an internal index; lengths zero and one fail. -/
theorem two_le_length (p : SimplePath G s t) (w : V → ℝ≥0) (hp : 1 ≤ p.weight w) :
    2 ≤ p.edgeLength := by
  have hne : p.internalVertices.Nonempty := by
    apply Finset.nonempty_iff_ne_empty.mpr
    intro h
    simp [SimplePath.weight, h] at hp
  obtain ⟨v, hv⟩ := hne
  obtain ⟨⟨i, rfl⟩, hs, ht⟩ := (p.mem_internalVertices v).mp hv
  have hi : i.val ≠ 0 := by
    intro h
    have he : i = 0 := Fin.ext h
    exact hs (by simpa only [he] using p.source_eq)
  have hj : i.val ≠ p.edgeLength := by
    intro h
    have he : i = Fin.last p.edgeLength := Fin.ext h
    exact ht (by simpa only [he] using p.target_eq)
  have := i.isLt
  omega

def first (p : SimplePath G s t) (hn : 2 ≤ p.edgeLength) : V :=
  p.vertex ⟨1, by omega⟩

def last (p : SimplePath G s t) (hn : 2 ≤ p.edgeLength) : V :=
  p.vertex ⟨p.edgeLength - 1, by omega⟩

omit [Fintype V] in
theorem first_internal (p : SimplePath G s t) (hn : 2 ≤ p.edgeLength) :
    first p hn ∈ p.internalVertices := index_internal p _ (by simp) (by dsimp; omega)

omit [Fintype V] in
theorem last_internal (p : SimplePath G s t) (hn : 2 ≤ p.edgeLength) :
    last p hn ∈ p.internalVertices := index_internal p _ (by dsimp; omega) (by dsimp; omega)

omit [Fintype V] [DecidableEq V] in
theorem first_adj (p : SimplePath G s t) (hn : 2 ≤ p.edgeLength) :
    G.Adj s (first p hn) := by
  have h := p.adjacent ⟨0, by omega⟩
  rw [show (⟨0, by omega⟩ : Fin p.edgeLength).castSucc = 0 by rfl, p.source_eq] at h
  exact h

omit [Fintype V] [DecidableEq V] in
theorem last_adj (p : SimplePath G s t) (hn : 2 ≤ p.edgeLength) :
    G.Adj (last p hn) t := by
  have h := p.adjacent ⟨p.edgeLength - 1, by omega⟩
  have he : (⟨p.edgeLength - 1, by omega⟩ : Fin p.edgeLength).succ =
      Fin.last p.edgeLength := by apply Fin.ext; dsimp; omega
  rw [he, p.target_eq] at h
  exact h

omit [Fintype V] in
/-- The threshold lower bound transfers to the first and last INTERNAL
vertices. An arbitrary path between them is closed with the two original
edges, and loop erasure supplies a genuine original demand path. -/
theorem internal_distance_lower (p : SimplePath G s t) (hn : 2 ≤ p.edgeLength)
    (w : V → ℝ≥0) (τ : ℝ≥0) (hst : 1 ≤ vertexDistance G w s t)
    (ha : w (first p hn) ≤ τ) (hb : w (last p hn) ≤ τ) :
    ((1 - 2 * τ : ℝ≥0) : ℝ≥0∞) ≤ vertexDistance G w (first p hn) (last p hn) := by
  apply (coe_le_vertexDistance_iff _ _ _ _ _).mpr
  intro q
  have hsa : s ≠ first p hn := ((p.mem_internalVertices _).mp (first_internal p hn)).2.1.symm
  have hbt : last p hn ≠ t := ((p.mem_internalVertices _).mp (last_internal p hn)).2.2
  let a := SimplePath.edge (first_adj p hn) hsa
  let b := SimplePath.edge (last_adj p hn) hbt
  obtain ⟨r, _, hr⟩ := a.exists_composition_weight_le q w
  obtain ⟨z, _, hz⟩ := r.exists_composition_weight_le b w
  have hlow : 1 ≤ z.weight w :=
    (coe_le_vertexDistance_iff G w s t 1).mp hst z
  have ha0 : a.weight w = 0 := SimplePath.edge_weight _ _ _
  have hb0 : b.weight w = 0 := SimplePath.edge_weight _ _ _
  rw [ha0, zero_add] at hr
  rw [hb0, add_zero] at hz
  apply (tsub_le_iff_right).mpr
  linarith

def firstSurvivor (p : SimplePath G s t) (hn : 2 ≤ p.edgeLength)
    (w : V → ℝ≥0) (τ : ℝ≥0) (hp : p.Avoids (heavy w τ)) : Residual w τ :=
  ⟨first p hn, hp _ (first_internal p hn)⟩

def lastSurvivor (p : SimplePath G s t) (hn : 2 ≤ p.edgeLength)
    (w : V → ℝ≥0) (τ : ℝ≥0) (hp : p.Avoids (heavy w τ)) : Residual w τ :=
  ⟨last p hn, hp _ (last_internal p hn)⟩

/-- A genuine residual subpath, including the length-zero trimmed case. -/
def trim (p : SimplePath G s t) (hn : 2 ≤ p.edgeLength)
    (w : V → ℝ≥0) (τ : ℝ≥0) (hp : p.Avoids (heavy w τ)) :
    SimplePath (graph G w τ) (firstSurvivor p hn w τ hp) (lastSurvivor p hn w τ hp) where
  edgeLength := p.edgeLength - 2
  vertex j := ⟨p.vertex ⟨j.val + 1, by have := j.isLt; omega⟩,
    hp _ (index_internal p _ (by dsimp; omega) (by dsimp; have := j.isLt; omega))⟩
  source_eq := Subtype.ext rfl
  target_eq := by
    apply Subtype.ext
    change p.vertex _ = p.vertex _
    congr 1
    apply Fin.ext
    dsimp
    omega
  injective := by
    intro i j h
    have he := congrArg Fin.val (p.injective (congrArg Subtype.val h))
    apply Fin.ext
    dsimp at he
    omega
  adjacent := by
    intro i
    exact p.adjacent ⟨i.val + 1, by have := i.isLt; omega⟩

theorem trim_vertex_internal (p : SimplePath G s t) (hn : 2 ≤ p.edgeLength)
    (w : V → ℝ≥0) (τ : ℝ≥0) (hp : p.Avoids (heavy w τ))
    (i : Fin ((trim p hn w τ hp).edgeLength + 1)) :
    ((trim p hn w τ hp).vertex i).val ∈ p.internalVertices := by
  apply index_internal p _ (by dsimp [trim]; omega)
  have hi := i.isLt
  change i.val < p.edgeLength - 2 + 1 at hi
  dsimp [trim]
  omega

end Path

/-- Forgetting the residual subtype preserves adjacency and simplicity. -/
def forgetPath {G : Digraph V} {w : V → ℝ≥0} {τ : ℝ≥0} {a b : Residual w τ}
    (q : SimplePath (graph G w τ) a b) : SimplePath G a.val b.val where
  edgeLength := q.edgeLength
  vertex i := (q.vertex i).val
  source_eq := congrArg Subtype.val q.source_eq
  target_eq := congrArg Subtype.val q.target_eq
  injective := fun _ _ h => q.injective (Subtype.ext h)
  adjacent := q.adjacent

theorem forgetPath_internalVertices {G : Digraph V} {w : V → ℝ≥0} {τ : ℝ≥0}
    {a b : Residual w τ} (q : SimplePath (graph G w τ) a b) :
    (forgetPath q).internalVertices = q.internalVertices.image Subtype.val := by
  ext v
  constructor
  · intro hv
    obtain ⟨⟨i, hi⟩, ha, hb⟩ := ((forgetPath q).mem_internalVertices v).mp hv
    refine Finset.mem_image.mpr ⟨q.vertex i, (q.mem_internalVertices _).mpr ?_, hi⟩
    exact ⟨⟨i, rfl⟩, fun h => ha (hi.symm.trans (congrArg Subtype.val h)),
      fun h => hb (hi.symm.trans (congrArg Subtype.val h))⟩
  · intro hv
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hv
    obtain ⟨⟨i, hi⟩, ha, hb⟩ := (q.mem_internalVertices x).mp hx
    exact ((forgetPath q).mem_internalVertices _).mpr
      ⟨⟨i, congrArg Subtype.val hi⟩, fun h => ha (Subtype.ext h), fun h => hb (Subtype.ext h)⟩

theorem residual_path_weight {G : Digraph V} {w : V → ℝ≥0} {τ : ℝ≥0}
    {a b : Residual w τ} (q : SimplePath (graph G w τ) a b) :
    q.weight (weight w τ) = 2 * (forgetPath q).weight w := by
  rw [SimplePath.weight, SimplePath.weight, forgetPath_internalVertices]
  rw [Finset.sum_image]
  · simp only [weight, Finset.mul_sum]
  · intro a _ b _ h
    exact Subtype.ext h

/-- The first and last internal vertices of any avoiding original demand
path form a threshold pair in the doubled residual graph. -/
theorem trimmed_threshold {G : Digraph V} {w : V → ℝ≥0} {τ : ℝ≥0}
    (hτ : τ ≤ 1 / 4) {s t : V} (p : SimplePath G s t) (hn : 2 ≤ p.edgeLength)
    (hp : p.Avoids (heavy w τ)) (hst : 1 ≤ vertexDistance G w s t) :
    1 ≤ vertexDistance (graph G w τ) (weight w τ)
      (Path.firstSurvivor p hn w τ hp) (Path.lastSurvivor p hn w τ hp) := by
  have ha := (survivor_weight_lt (Path.firstSurvivor p hn w τ hp)).le
  have hb := (survivor_weight_lt (Path.lastSurvivor p hn w τ hp)).le
  have hd := Path.internal_distance_lower p hn w τ hst ha hb
  apply (coe_le_vertexDistance_iff _ _ _ _ 1).mpr
  intro q
  have hq := (coe_le_vertexDistance_iff _ _ _ _ _).mp hd (forgetPath q)
  have hhalf : (1 / 2 : ℝ≥0) ≤ 1 - 2 * τ := by
    apply (le_tsub_iff_right (show 2 * τ ≤ 1 by linarith)).mpr
    linarith
  rw [residual_path_weight]
  have hhalfq : (1 / 2 : ℝ≥0) ≤ (forgetPath q).weight w := hhalf.trans hq
  have hdouble := mul_le_mul_of_nonneg_left hhalfq (show (0 : ℝ≥0) ≤ 2 by norm_num)
  norm_num at hdouble
  exact hdouble

/-- Actual all-pairs cut transfer, even if either original endpoint is heavy. -/
theorem combined_isIntegralCut {G : Digraph V} {w : V → ℝ≥0} {τ : ℝ≥0}
    (hτ : τ ≤ 1 / 4) (Y : Finset (Residual w τ))
    (hY : IsIntegralCut (graph G w τ) Y (thresholdDemands (graph G w τ) (weight w τ))) :
    IsIntegralCut G (combinedCut w τ Y) (thresholdDemands G w) := by
  intro s t hst p
  by_cases hp : ∃ v ∈ p.internalVertices, v ∈ heavy w τ
  · obtain ⟨v, hv, hh⟩ := hp
    exact ⟨v, hv, Finset.mem_union_left _ hh⟩
  · have hav : p.Avoids (heavy w τ) := fun v hv hh => hp ⟨v, hv, hh⟩
    have hweight : 1 ≤ p.weight w := (coe_le_vertexDistance_iff G w s t 1).mp hst p
    have hn := Path.two_le_length p w hweight
    have hd := trimmed_threshold hτ p hn hav hst
    obtain ⟨v, hv, hvY⟩ := hY _ _ hd (Path.trim p hn w τ hav)
    obtain ⟨⟨i, hi⟩, _, _⟩ := ((Path.trim p hn w τ hav).mem_internalVertices v).mp hv
    refine ⟨v.val, ?_, Finset.mem_union_right _ (Finset.mem_image.mpr ⟨v, hvY, rfl⟩)⟩
    rw [← hi]
    exact Path.trim_vertex_internal p hn w τ hav i

/-- A bounded arbitrary-cost residual rounding oracle. It covers zero weight,
zero objective, and empty instances, and keeps both finite bounds explicit. -/
def BoundedRoundingOracle (N : ℕ) (B α : ℝ≥0) : Prop :=
  ∀ (U : Type u) [Fintype U] [DecidableEq U] (H : Digraph U) (z d : U → ℝ≥0),
    Fintype.card U ≤ N → totalWeight z ≤ B →
    ∃ Y : Finset U, IsIntegralCut H Y (thresholdDemands H z) ∧
      cutCost d Y ≤ α * weightedCost d z

/-- Finite self-reduction with the explicit factor `1/τ + 2α`. -/
theorem round_of_bounded_oracle (G : Digraph V) (w c : V → ℝ≥0)
    (τ α : ℝ≥0) (hτpos : 0 < τ) (hτ : τ ≤ 1 / 4)
    (oracle : BoundedRoundingOracle.{u} (Fintype.card V)
      (2 * (Fintype.card V : ℝ≥0) * τ) α) :
    ∃ X : Finset V, IsIntegralCut G X (thresholdDemands G w) ∧
      cutCost c X ≤ (1 / τ + 2 * α) * weightedCost c w := by
  obtain ⟨Y, hY, hcost⟩ := oracle (Residual w τ) (graph G w τ) (weight w τ) (cost w c τ)
    (residual_card_le w τ) (residual_totalWeight_le w τ)
  refine ⟨combinedCut w τ Y, combined_isIntegralCut hτ Y hY, ?_⟩
  rw [combined_cutCost]
  calc
    _ ≤ weightedCost c w / τ + α * weightedCost (cost w c τ) (weight w τ) :=
      add_le_add (heavy_cutCost_le w c τ hτpos) hcost
    _ ≤ weightedCost c w / τ + α * (2 * weightedCost c w) :=
      add_le_add_right (mul_le_mul_of_nonneg_left (residual_weightedCost_le w c τ) zero_le) _
    _ = _ := by ring

/-- The finite reduction supplies the established graph rounding interface. -/
theorem hasVertexRoundingFactor_of_bounded_oracle (G : Digraph V) (w : V → ℝ≥0)
    (τ α : ℝ≥0) (hτpos : 0 < τ) (hτ : τ ≤ 1 / 4)
    (oracle : BoundedRoundingOracle.{u} (Fintype.card V)
      (2 * (Fintype.card V : ℝ≥0) * τ) α) :
    HasVertexRoundingFactor G w ((1 / τ + 2 * α : ℝ≥0) : ℝ) := by
  refine ⟨NNReal.coe_nonneg _, ?_⟩
  intro c
  obtain ⟨X, hX, hcost⟩ := round_of_bounded_oracle G w c τ α hτpos hτ oracle
  exact ⟨X, hX, by exact_mod_cast hcost⟩

/-- The paper's threshold, with real exponent and explicit factor four. -/
def powerThreshold (n : ℕ) (c : ℝ) : ℝ≥0 :=
  1 / (4 * (n : ℝ≥0) ^ (c / (1 + c)))

theorem powerThreshold_pos (n : ℕ) (hn : 1 ≤ n) (c : ℝ) :
    0 < powerThreshold n c := by
  dsimp [powerThreshold]
  apply div_pos zero_lt_one
  apply mul_pos (by norm_num)
  apply NNReal.rpow_pos
  exact_mod_cast hn

theorem powerThreshold_le_quarter (n : ℕ) (hn : 1 ≤ n) (c : ℝ) (hc : 0 ≤ c) :
    powerThreshold n c ≤ 1 / 4 := by
  have hpow : (1 : ℝ≥0) ≤ (n : ℝ≥0) ^ (c / (1 + c)) :=
    NNReal.one_le_rpow (by exact_mod_cast hn) (by positivity)
  dsimp [powerThreshold]
  exact div_le_div_of_nonneg_left zero_le (by norm_num) (by nlinarith)

/-- The true finite residual mass is at most `n^(1/(1+c))`. -/
theorem powerThreshold_budget (n : ℕ) (hn : 1 ≤ n) (c : ℝ) (hc : 0 ≤ c) :
    2 * (n : ℝ≥0) * powerThreshold n c ≤ (n : ℝ≥0) ^ (1 / (1 + c)) := by
  have hnpos : (0 : ℝ≥0) < n := by exact_mod_cast hn
  have hA : (0 : ℝ≥0) < (n : ℝ≥0) ^ (c / (1 + c)) := NNReal.rpow_pos hnpos
  have hden : (1 + c) ≠ 0 := by positivity
  have hexp : c / (1 + c) + 1 / (1 + c) = 1 := by field_simp; ring
  have hprod : (n : ℝ≥0) ^ (c / (1 + c)) * (n : ℝ≥0) ^ (1 / (1 + c)) = n := by
    rw [← NNReal.rpow_add hnpos.ne', hexp, NNReal.rpow_one]
  calc
    _ = (n : ℝ≥0) / (2 * (n : ℝ≥0) ^ (c / (1 + c))) := by
      dsimp [powerThreshold]
      field_simp
      ring
    _ ≤ (n : ℝ≥0) / (n : ℝ≥0) ^ (c / (1 + c)) :=
      div_le_div_of_nonneg_left zero_le hA (by nlinarith)
    _ = _ := (div_eq_iff hA.ne').mpr (by simpa only [mul_comm] using hprod.symm)

/-- A uniform power estimate stated as an actual graph rounding oracle.
The exponent is real; this makes no `o(1)` or efficiency assertion. -/
def PowerRoundingOracle (c : ℝ) (K : ℝ≥0) : Prop :=
  ∀ (U : Type u) [Fintype U] [DecidableEq U] (H : Digraph U) (z d : U → ℝ≥0),
    ∃ Y : Finset U, IsIntegralCut H Y (thresholdDemands H z) ∧
      cutCost d Y ≤ (K * (totalWeight z) ^ c) * weightedCost d z

/-- Exact finite real-power specialization. A `K W^c` oracle gives
`(4+2K) n^(c/(1+c))`, for every `n ≥ 1` and real `c ≥ 0`.
At `c=0`, the library's ordinary real-power convention is `0^0=1`.
This statement does not assert the source's asymptotic or runtime conclusion. -/
theorem round_of_power_oracle (G : Digraph V) (w d : V → ℝ≥0)
    (hn : 1 ≤ Fintype.card V) (c : ℝ) (hc : 0 ≤ c) (K : ℝ≥0)
    (oracle : PowerRoundingOracle.{u} c K) :
    ∃ X : Finset V, IsIntegralCut G X (thresholdDemands G w) ∧
      cutCost d X ≤ ((4 + 2 * K) * (Fintype.card V : ℝ≥0) ^ (c / (1 + c))) *
        weightedCost d w := by
  let n := Fintype.card V
  let A : ℝ≥0 := (n : ℝ≥0) ^ (c / (1 + c))
  let τ := powerThreshold n c
  have hbound : BoundedRoundingOracle.{u} n (2 * (n : ℝ≥0) * τ) (K * A) := by
    intro U _ _ H z costU _hcard hmass
    obtain ⟨Y, hY, hcost⟩ := oracle U H z costU
    refine ⟨Y, hY, hcost.trans ?_⟩
    have hm : totalWeight z ≤ (n : ℝ≥0) ^ (1 / (1 + c)) :=
      hmass.trans (powerThreshold_budget n hn c hc)
    have hp : (totalWeight z) ^ c ≤ A := by
      calc
        _ ≤ ((n : ℝ≥0) ^ (1 / (1 + c))) ^ c := NNReal.rpow_le_rpow hm hc
        _ = A := by rw [← NNReal.rpow_mul]; congr 1; ring
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hp zero_le) zero_le
  obtain ⟨X, hX, hcost⟩ := round_of_bounded_oracle G w d τ (K * A)
    (powerThreshold_pos n hn c) (powerThreshold_le_quarter n hn c hc) hbound
  refine ⟨X, hX, ?_⟩
  have hfactor : 1 / τ + 2 * (K * A) = (4 + 2 * K) * A := by
    dsimp [τ, powerThreshold, A]
    rw [one_div_one_div]
    ring
  rw [hfactor] at hcost
  exact hcost

end WeightSelfReduction
end
end DirectedFlowCutGap
