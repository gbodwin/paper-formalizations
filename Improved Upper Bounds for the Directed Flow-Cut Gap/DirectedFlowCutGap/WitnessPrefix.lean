import DirectedFlowCutGap.LevelCut
import DirectedFlowCutGap.WitnessThinning

/-!
# Endpoint-safe first-crossing prefixes

Graph-backed input for the honest greedy scan. The carrier avoids the current
cut only internally: its original endpoints may be deleted. The source is
omitted from the scan with increment budget zero, since its first edge has
internal-vertex distance zero. The prefix ends immediately before the first
height at least one; earlier heights need not be monotone.

This module does not assert maximal witness-family construction, candidate
comparison, or the complete witness lemma.
-/

namespace DirectedFlowCutGap

noncomputable section

open scoped BigOperators NNReal ENNReal

namespace WitnessPrefix

variable {V : Type*} [DecidableEq V] [Fintype V]
variable {G : Digraph V} {s t : V}

/-- Extend the indexed vertex sequence to natural indices by clamping at its
target. All scan statements below supply bounds preventing clamping. -/
def vertex (p : SimplePath G s t) (i : ℕ) : V :=
  p.vertex ⟨min i p.edgeLength, by omega⟩

omit [DecidableEq V] [Fintype V] in
@[simp] theorem vertex_zero (p : SimplePath G s t) : vertex p 0 = s := by
  simpa [vertex] using p.source_eq

omit [DecidableEq V] [Fintype V] in
@[simp] theorem vertex_last (p : SimplePath G s t) : vertex p p.edgeLength = t := by
  simpa [vertex, Fin.last] using p.target_eq

omit [DecidableEq V] [Fintype V] in
theorem vertex_eq (p : SimplePath G s t) (i : ℕ) (hi : i ≤ p.edgeLength) :
    vertex p i = p.vertex ⟨i, by omega⟩ := by
  simp [vertex, Nat.min_eq_left hi]

omit [DecidableEq V] [Fintype V] in
theorem vertex_injective (p : SimplePath G s t) {i j : ℕ}
    (hi : i ≤ p.edgeLength) (hj : j ≤ p.edgeLength)
    (h : vertex p i = vertex p j) : i = j := by
  rw [vertex_eq p i hi, vertex_eq p j hj] at h
  exact congrArg Fin.val (p.injective h)

omit [DecidableEq V] [Fintype V] in
theorem vertex_adjacent (p : SimplePath G s t) {i : ℕ} (hi : i < p.edgeLength) :
    G.Adj (vertex p i) (vertex p (i + 1)) := by
  rw [vertex_eq p i (by omega), vertex_eq p (i + 1) (by omega)]
  exact p.adjacent ⟨i, hi⟩

omit [Fintype V] in
theorem vertex_internal (p : SimplePath G s t) {i : ℕ}
    (hi0 : 0 < i) (hi : i < p.edgeLength) : vertex p i ∈ p.internalVertices := by
  apply (p.mem_internalVertices _).mpr
  refine ⟨⟨⟨min i p.edgeLength, by omega⟩, rfl⟩, ?_, ?_⟩
  · intro hs
    have he := vertex_injective p (by omega : i ≤ p.edgeLength)
      (by omega : 0 ≤ p.edgeLength) (hs.trans (vertex_zero p).symm)
    omega
  · intro ht
    have he := vertex_injective p (by omega : i ≤ p.edgeLength)
      (le_refl _) (ht.trans (vertex_last p).symm)
    omega

/-- All distances used by the carrier's real-valued scan are finite. -/
theorem distance_lt_top (p : SimplePath G s t) (w : V → ℝ≥0) (i : ℕ) :
    vertexDistance G w s (vertex p i) < ⊤ := by
  have hall : ∀ j : Fin (p.edgeLength + 1),
      vertexDistance G w s (p.vertex j) < ⊤ := by
    intro j
    induction j using Fin.induction with
    | zero => simp [p.source_eq]
    | succ j ih =>
      exact lt_of_le_of_lt (vertexDistance_le_of_adj G w s (p.adjacent j))
        (ENNReal.add_lt_top.mpr ⟨ih, ENNReal.coe_lt_top⟩)
  exact hall _

/-- Original-graph frozen source distance along the actual carrier. -/
def height (p : SimplePath G s t) (w : V → ℝ≥0) (i : ℕ) : ℝ :=
  (vertexDistance G w s (vertex p i)).toReal

omit [Fintype V] in
theorem height_nonneg (p : SimplePath G s t) (w : V → ℝ≥0) (i : ℕ) :
    0 ≤ height p w i := ENNReal.toReal_nonneg

omit [Fintype V] in
@[simp] theorem height_zero (p : SimplePath G s t) (w : V → ℝ≥0) :
    height p w 0 = 0 := by simp [height]

omit [Fintype V] in
/-- The source's actual weight is irrelevant to the first increment. -/
theorem height_one (p : SimplePath G s t) (w : V → ℝ≥0)
    (hp : 0 < p.edgeLength) : height p w 1 = 0 := by
  have ha : G.Adj s (vertex p 1) := by
    simpa using vertex_adjacent p hp
  simp [height, vertexDistance_of_adj w ha]

theorem height_step (p : SimplePath G s t) (w : V → ℝ≥0)
    {i : ℕ} (hi : i < p.edgeLength) :
    height p w (i + 1) ≤ height p w i + (w (vertex p i) : ℝ) := by
  have h := vertexDistance_le_of_adj G w s (vertex_adjacent p hi)
  have hr := (ENNReal.toReal_le_toReal (distance_lt_top p w (i + 1)).ne
    (ENNReal.add_lt_top.mpr ⟨distance_lt_top p w i, ENNReal.coe_lt_top⟩).ne).mpr h
  simpa [height, ENNReal.toReal_add (distance_lt_top p w i).ne ENNReal.coe_ne_top]
    using hr

theorem one_le_height_last (p : SimplePath G s t) (w : V → ℝ≥0)
    (hcut : 1 ≤ vertexDistance G w s t) : 1 ≤ height p w p.edgeLength := by
  have hfinite : vertexDistance G w s t ≠ ⊤ := by
    simpa using (distance_lt_top p w p.edgeLength).ne
  have h := (ENNReal.toReal_le_toReal (by simp : (1 : ℝ≥0∞) ≠ ⊤) hfinite).mpr hcut
  simpa [height] using h

/-- `N` is the predecessor of the first height at least one. It is an internal
vertex, and every height at or before `N` is below one. -/
structure FirstCrossing (p : SimplePath G s t) (w : V → ℝ≥0) where
  N : ℕ
  positive : 0 < N
  before_target : N + 1 ≤ p.edgeLength
  before : ∀ i ≤ N, height p w i < 1
  crosses : 1 ≤ height p w (N + 1)

theorem exists_firstCrossing (p : SimplePath G s t) (w : V → ℝ≥0)
    (hcut : 1 ≤ vertexDistance G w s t) : Nonempty (FirstCrossing p w) := by
  classical
  have hex : ∃ j : ℕ, j ≤ p.edgeLength ∧ 1 ≤ height p w j :=
    ⟨p.edgeLength, le_refl _, one_le_height_last p w hcut⟩
  let j := Nat.find hex
  have hj : j ≤ p.edgeLength ∧ 1 ≤ height p w j := Nat.find_spec hex
  have hbefore : ∀ i < j, height p w i < 1 := by
    intro i hi
    apply lt_of_not_ge
    intro hh
    have : j ≤ i := Nat.find_min' hex ⟨by omega, hh⟩
    omega
  have hj0 : j ≠ 0 := by
    intro hz
    have hh := hj.2
    rw [hz, height_zero] at hh
    norm_num at hh
  have hm : 0 < p.edgeLength := by omega
  have hj1 : j ≠ 1 := by
    intro hz
    have hh := hj.2
    rw [hz, height_one p w hm] at hh
    norm_num at hh
  refine ⟨⟨j - 1, by omega, by omega, ?_, ?_⟩⟩
  · intro i hi
    exact hbefore i (by omega)
  · simpa only [Nat.sub_add_cancel (by omega : 1 ≤ j)] using hj.2

/-- Source-safe increment budget: deleting the source costs zero. -/
def increment (p : SimplePath G s t) (w : V → ℝ≥0) (i : ℕ) : ℝ :=
  if i = 0 then 0 else (w (vertex p i) : ℝ)

/-- Used vertices are deleted, and the original source is always omitted. -/
def deleted (p : SimplePath G s t) (U : Finset V) (i : ℕ) : Prop :=
  i = 0 ∨ vertex p i ∈ U

omit [DecidableEq V] [Fintype V] in
theorem increment_nonneg (p : SimplePath G s t) (w : V → ℝ≥0) (i : ℕ) :
    0 ≤ increment p w i := by
  unfold increment
  split_ifs <;> positivity

theorem source_safe_step (p : SimplePath G s t) (w : V → ℝ≥0)
    {i : ℕ} (hi : i < p.edgeLength) :
    height p w (i + 1) ≤ height p w i + increment p w i := by
  by_cases hiz : i = 0
  · subst i
    simp [increment, height_one p w hi]
  · simpa [increment, hiz] using height_step p w hi

namespace FirstCrossing

variable {p : SimplePath G s t} {w : V → ℝ≥0}

omit [Fintype V] in
theorem increment_le (c : FirstCrossing p w) {X : Finset V}
    (havoid : p.Avoids X) {L B : ℝ} (hB : 0 ≤ B) (hL : 0 < L)
    (hcap : ∀ v ∉ X, (w v : ℝ) ≤ B / L) {i : ℕ} (hi : i < c.N) :
    increment p w i ≤ B / L := by
  by_cases hiz : i = 0
  · simp only [increment, ite_eq_left hiz]
    positivity
  · have hint := vertex_internal p (by omega : 0 < i)
      (by have := c.before_target; omega : i < p.edgeLength)
    simpa only [increment, ite_eq_right hiz] using hcap _ (havoid _ hint)

theorem terminal_lower (c : FirstCrossing p w) {X : Finset V}
    (havoid : p.Avoids X) {L B : ℝ}
    (hcap : ∀ v ∉ X, (w v : ℝ) ≤ B / L) :
    1 - B / L ≤ height p w c.N := by
  have hN : c.N < p.edgeLength := by have := c.before_target; omega
  have hi := vertex_internal p c.positive hN
  have hw := hcap _ (havoid _ hi)
  have hs := height_step p w hN
  have hc := c.crosses
  linarith

omit [Fintype V] in
/-- Only genuinely used internal vertices contribute to the deleted budget;
the forcibly omitted source contributes zero. -/
theorem deletedWeight_le (c : FirstCrossing p w) (U : Finset V) :
    WitnessThinning.deletedWeight (increment p w) (deleted p U) c.N ≤
      ∑ v ∈ p.internalVertices ∩ U, (w v : ℝ) := by
  classical
  let I := (Finset.range c.N).filter (fun i => i ≠ 0 ∧ vertex p i ∈ U)
  have hsum : WitnessThinning.deletedWeight (increment p w) (deleted p U) c.N =
      ∑ i ∈ I, (w (vertex p i) : ℝ) := by
    rw [WitnessThinning.deletedWeight]
    dsimp only [I]
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro i hi
    by_cases hiz : i = 0
    · simp [increment, deleted, hiz]
    · by_cases hiU : vertex p i ∈ U <;> simp [increment, deleted, hiz, hiU]
  have hinj : Set.InjOn (vertex p) (I : Set ℕ) := by
    intro i hi j hj heq
    have hiN := Finset.mem_range.mp (Finset.mem_filter.mp hi).1
    have hjN := Finset.mem_range.mp (Finset.mem_filter.mp hj).1
    exact vertex_injective p (by have := c.before_target; omega)
      (by have := c.before_target; omega) heq
  have hsub : I.image (vertex p) ⊆ p.internalVertices ∩ U := by
    intro v hv
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hv
    obtain ⟨hiN, hiz, hiU⟩ := Finset.mem_filter.mp hi
    have hiN := Finset.mem_range.mp hiN
    exact Finset.mem_inter.mpr
      ⟨vertex_internal p (by omega) (by have := c.before_target; omega), hiU⟩
  have himage : (∑ v ∈ I.image (vertex p), (w v : ℝ)) =
      ∑ i ∈ I, (w (vertex p i) : ℝ) := Finset.sum_image hinj
  rw [hsum, ← himage]
  exact Finset.sum_le_sum_of_subset_of_nonneg hsub
    (fun v _ _ => (w v).coe_nonneg)

/-- The actual graph prefix satisfies every numeric hypothesis, giving the
source-scale length bounds for its concrete ordered scan. -/
theorem scan_bounds (c : FirstCrossing p w) {X U : Finset V}
    (havoid : p.Avoids X) {L B : ℝ} (hB : 1 ≤ B) (hL : 64 * B ≤ L)
    (hcap : ∀ v ∉ X, (w v : ℝ) ≤ B / L)
    (hused : (∑ v ∈ p.internalVertices ∩ U, (w v : ℝ)) < 1 / 4) :
    let selected := (WitnessThinning.scan (height p w) (deleted p U) (1 / L) c.N).selected
    selected ≠ [] ∧ L / (4 * B) ≤ ((selected.length - 1 : ℕ) : ℝ) ∧
      ((selected.length - 1 : ℕ) : ℝ) ≤ L := by
  have hLpos : 0 < L := by linarith
  have hBnonneg : 0 ≤ B := by linarith
  apply WitnessThinning.source_scale_bounds _ _ _ c.N hB hL (height_zero p w)
  · intro i hi
    exact ⟨increment_nonneg p w i, c.increment_le havoid hBnonneg hLpos hcap hi⟩
  · intro i hi
    exact source_safe_step p w (by have := c.before_target; omega)
  · exact c.terminal_lower havoid hcap
  · have hh := c.deletedWeight_le U
    have hBU : 0 ≤ B / L := by positivity
    linarith
  · intro i hi
    exact (c.before i (by omega)).le

omit [Fintype V] in
/-- Selected vertices really are new internal vertices, not merely vertices
of a demand-specific residual graph. -/
theorem selected_internal (c : FirstCrossing p w) {X U : Finset V}
    (havoid : p.Avoids X) (h : ℝ) {i : ℕ}
    (hi : i ∈ (WitnessThinning.scan (height p w) (deleted p U) h c.N).selected) :
    vertex p i ∈ p.internalVertices ∧ vertex p i ∉ X ∧ vertex p i ∉ U := by
  obtain ⟨hiN, hdel⟩ := WitnessThinning.selected_mem _ _ _ _ i hi
  have hiz : i ≠ 0 := fun hz => hdel (Or.inl hz)
  have hint := vertex_internal p (by omega : 0 < i)
    (by have := c.before_target; omega : i < p.edgeLength)
  exact ⟨hint, havoid _ hint, fun hiU => hdel (Or.inr hiU)⟩

/-- The mapped scan is an actual vertex list; labels belong to the enclosing
witness-family construction rather than to the endpoints of this list. -/
def selectedVertices (c : FirstCrossing p w) (U : Finset V) (h : ℝ) : List V :=
  (WitnessThinning.scan (height p w) (deleted p U) h c.N).selected.map (vertex p)

omit [Fintype V] in
theorem selectedVertices_nodup (c : FirstCrossing p w) (U : Finset V) (h : ℝ) :
    (c.selectedVertices U h).Nodup := by
  apply List.Nodup.map_on
  · intro i hi j hj hij
    have hiN := (WitnessThinning.selected_mem _ _ _ _ i hi).1
    have hjN := (WitnessThinning.selected_mem _ _ _ _ j hj).1
    exact vertex_injective p (by have := c.before_target; omega)
      (by have := c.before_target; omega) hij
  · exact (WitnessThinning.selected_increasing _ _ _ _).imp
      (fun hlt => Nat.ne_of_lt hlt)

omit [Fintype V] in
theorem selectedVertices_internal (c : FirstCrossing p w) {X U : Finset V}
    (havoid : p.Avoids X) (h : ℝ) {v : V}
    (hv : v ∈ c.selectedVertices U h) :
    v ∈ p.internalVertices ∧ v ∉ X ∧ v ∉ U := by
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hv
  exact c.selected_internal havoid h hi

omit [Fintype V] in
theorem selectedVertices_height_lt_one (c : FirstCrossing p w) (U : Finset V)
    (h : ℝ) {v : V} (hv : v ∈ c.selectedVertices U h) :
    (vertexDistance G w s v).toReal < 1 := by
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hv
  have hiN := (WitnessThinning.selected_mem _ _ _ _ i hi).1
  exact c.before i (by omega)

omit [Fintype V] in
theorem selectedVertices_separated (c : FirstCrossing p w) (U : Finset V)
    {h : ℝ} (hh : 0 ≤ h) :
    (c.selectedVertices U h).Pairwise (fun u v =>
      (vertexDistance G w s u).toReal + h ≤ (vertexDistance G w s v).toReal) := by
  simpa only [selectedVertices, List.pairwise_map, height] using
    WitnessThinning.selected_separated (height p w) (deleted p U) hh c.N

theorem selectedVertices_bounds (c : FirstCrossing p w) {X U : Finset V}
    (havoid : p.Avoids X) {L B : ℝ} (hB : 1 ≤ B) (hL : 64 * B ≤ L)
    (hcap : ∀ v ∉ X, (w v : ℝ) ≤ B / L)
    (hused : (∑ v ∈ p.internalVertices ∩ U, (w v : ℝ)) < 1 / 4) :
    c.selectedVertices U (1 / L) ≠ [] ∧
      L / (4 * B) ≤ (((c.selectedVertices U (1 / L)).length - 1 : ℕ) : ℝ) ∧
      (((c.selectedVertices U (1 / L)).length - 1 : ℕ) : ℝ) ≤ L := by
  simpa only [selectedVertices, List.length_map, ne_eq, List.map_eq_nil_iff] using
    c.scan_bounds havoid hB hL hcap hused

end FirstCrossing

/-- The common residual graph deletes every vertex in `X`, irrespective of
which demand label supplied a carrier. -/
def residualGraph (G : Digraph V) (X : Finset V) : Digraph {v : V // v ∉ X} where
  Adj u v := G.Adj u.val v.val

/-- The whole interval between two internal carrier vertices survives in the
common residual graph, even if the carrier's original endpoints are deleted. -/
def residualSegment (p : SimplePath G s t) {X : Finset V} (havoid : p.Avoids X)
    (i j : ℕ) (hi0 : 0 < i) (hij : i ≤ j) (hj : j < p.edgeLength) :
    SimplePath (residualGraph G X)
      ⟨vertex p i, havoid _ (vertex_internal p hi0 (by omega))⟩
      ⟨vertex p j, havoid _ (vertex_internal p (by omega) hj)⟩ where
  edgeLength := j - i
  vertex k := ⟨vertex p (i + k.val),
    havoid _ (vertex_internal p (by omega) (by have := k.isLt; omega))⟩
  source_eq := by apply Subtype.ext; simp
  target_eq := by
    apply Subtype.ext
    simp only [Fin.val_last]
    congr 1
    omega
  injective := by
    intro a b hab
    have heq := congrArg Subtype.val hab
    have ha := a.isLt
    have hb := b.isLt
    have he := vertex_injective p (by omega : i + a.val ≤ p.edgeLength)
      (by omega : i + b.val ≤ p.edgeLength) heq
    apply Fin.ext
    omega
  adjacent := by
    intro k
    have hk := k.isLt
    exact vertex_adjacent p (by omega : i + k.val < p.edgeLength)

omit [Fintype V] in
theorem selected_reachable_in_residual {p : SimplePath G s t} {w : V → ℝ≥0}
    (c : FirstCrossing p w) {X U : Finset V} (havoid : p.Avoids X)
    (h : ℝ) {i j : ℕ}
    (hi : i ∈ (WitnessThinning.scan (height p w) (deleted p U) h c.N).selected)
    (hj : j ∈ (WitnessThinning.scan (height p w) (deleted p U) h c.N).selected)
    (hij : i ≤ j) :
    Nonempty (SimplePath (residualGraph G X)
      ⟨vertex p i, (c.selected_internal havoid h hi).2.1⟩
      ⟨vertex p j, (c.selected_internal havoid h hj).2.1⟩) := by
  obtain ⟨hiN, hdel⟩ := WitnessThinning.selected_mem _ _ _ _ i hi
  have hi0 : 0 < i := by
    have hiz : i ≠ 0 := fun hz => hdel (Or.inl hz)
    omega
  have hjN := (WitnessThinning.selected_mem _ _ _ _ j hj).1
  exact ⟨residualSegment p havoid i j hi0 hij (by have := c.before_target; omega)⟩

end WitnessPrefix

end

end DirectedFlowCutGap
