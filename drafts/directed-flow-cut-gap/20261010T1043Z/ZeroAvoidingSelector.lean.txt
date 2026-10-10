import DirectedFlowCutGap.ZeroWeights
import DirectedFlowCutGap.EdgeModel
import DirectedFlowCutGap.RawNonnegativeRational
import DirectedFlowCutGap.EncodedRoundingInput

/-!
# Zero avoidance without encoding the approximation factor

Let `S` be the positive support of the original weights. Charge every resource
outside `S` the sum of the current costs on `S`, plus one. Compare the returned
cut's actual penalized cost with the cost of `S`, retaining the cheaper cut.
The result lies in `S`, independently of the oracle's cost guarantee. On an
oracle-success event its original cost satisfies the unchanged `α` guarantee.
Neither the penalty nor its executable comparison uses `α`.

The graph lemmas prove that positive support is an original-graph valid cut;
the edge support contains actual edges only. The raw implementation reuses the
retained finite scans and word-operation model. Its `none` branch returns the
valid support fallback, but does NOT acquire an approximation guarantee from a
failed oracle. It does not implement oracle validity checking, a binary-cost
refinement, the graph-resource indexing join, or the adaptive MW composition.
-/

namespace DirectedFlowCutGap.ZeroAvoidingSelector

open scoped BigOperators NNReal NNRat

section Finite

variable {E : Type*} [Fintype E] [DecidableEq E]

noncomputable def positiveSupport (w : E → ℝ) : Finset E :=
  Finset.univ.filter fun e => 0 < w e

omit [DecidableEq E] in
@[simp] theorem mem_positiveSupport (w : E → ℝ) (e : E) :
    e ∈ positiveSupport w ↔ 0 < w e := by
  classical
  simp [positiveSupport]

noncomputable def penalty (S : Finset E) (c : E → ℝ) (e : E) : ℝ :=
  if e ∈ S then c e else (∑ a ∈ S, c a) + 1

noncomputable def choose (S : Finset E) (c : E → ℝ) (X : Finset E) : Finset E :=
  if (∑ e ∈ X, penalty S c e) ≤ ∑ e ∈ S, c e then X else S

omit [Fintype E] in
theorem penalty_nonneg (S : Finset E) (c : E → ℝ) (hc : ∀ e, 0 ≤ c e)
    (e : E) : 0 ≤ penalty S c e := by
  classical
  unfold penalty
  split_ifs
  · exact hc e
  · exact add_nonneg (Finset.sum_nonneg fun a _ => hc a) (by norm_num)

omit [Fintype E] in
theorem penalty_support_cost (S : Finset E) (c : E → ℝ) :
    (∑ e ∈ S, penalty S c e) = ∑ e ∈ S, c e := by
  classical
  apply Finset.sum_congr rfl
  intro e he
  simp [penalty, he]

omit [Fintype E] in
theorem choose_budget (S : Finset E) (c : E → ℝ) (X : Finset E) :
    (∑ e ∈ choose S c X, penalty S c e) ≤ ∑ e ∈ S, c e := by
  classical
  unfold choose
  split_ifs with h
  · exact h
  · exact le_of_eq (penalty_support_cost S c)

omit [Fintype E] in
theorem choose_subset (S : Finset E) (c : E → ℝ) (hc : ∀ e, 0 ≤ c e)
    (X : Finset E) : choose S c X ⊆ S := by
  classical
  intro e he
  by_contra hn
  have hs := Finset.single_le_sum (fun a _ => penalty_nonneg S c hc a) he
  have hb := choose_budget S c X
  have hz : penalty S c e = (∑ a ∈ S, c a) + 1 := by simp [penalty, hn]
  rw [hz] at hs
  linarith

omit [Fintype E] in
theorem choose_cost_eq (S : Finset E) (c : E → ℝ) (hc : ∀ e, 0 ≤ c e)
    (X : Finset E) :
    (∑ e ∈ choose S c X, c e) = ∑ e ∈ choose S c X, penalty S c e := by
  classical
  apply Finset.sum_congr rfl
  intro e he
  simp [penalty, choose_subset S c hc X he]

omit [Fintype E] in
theorem choose_cost_le (S : Finset E) (c : E → ℝ) (hc : ∀ e, 0 ≤ c e)
    (X : Finset E) :
    (∑ e ∈ choose S c X, c e) ≤ ∑ e ∈ X, penalty S c e := by
  classical
  rw [choose_cost_eq S c hc X]
  unfold choose
  split_ifs with h
  · exact le_rfl
  · rw [penalty_support_cost]
    exact (lt_of_not_ge h).le

omit [Fintype E] in
theorem choose_valid (S : Finset E) (c : E → ℝ) (X : Finset E)
    (P : Finset E → Prop) (hS : P S) (hX : P X) : P (choose S c X) := by
  classical
  unfold choose
  split_ifs
  · exact hX
  · exact hS

theorem penalty_potential (w c : E → ℝ) (hw : ∀ e, 0 ≤ w e) :
    mwPotential w (penalty (positiveSupport w) c) = mwPotential w c := by
  classical
  unfold mwPotential
  apply Finset.sum_congr rfl
  intro e _
  by_cases he : 0 < w e
  · simp [penalty, he]
  · have hz : w e = 0 := le_antisymm (le_of_not_gt he) (hw e)
    simp [hz]

/-- The original factor and original weights are unchanged. No lower bound on
`α` is used; in particular this theorem covers `α < 1` and `α = 0`. -/
theorem choose_preserves_oracle (w c : E → ℝ) (α : ℝ)
    (hw : ∀ e, 0 ≤ w e) (hc : ∀ e, 0 ≤ c e)
    (P : Finset E → Prop) (hS : P (positiveSupport w))
    (X : Finset E) (hX : P X)
    (hcost : (∑ e ∈ X, penalty (positiveSupport w) c e) ≤
      α * mwPotential w (penalty (positiveSupport w) c)) :
    P (choose (positiveSupport w) c X) ∧
      (∀ e ∈ choose (positiveSupport w) c X, 0 < w e) ∧
      (∑ e ∈ choose (positiveSupport w) c X, c e) ≤ α * mwPotential w c := by
  refine ⟨choose_valid _ _ _ P hS hX, ?_, ?_⟩
  · intro e he
    exact (mem_positiveSupport w e).mp (choose_subset _ _ hc X he)
  · exact (choose_cost_le _ _ hc X).trans
      (by simpa only [penalty_potential w c hw] using hcost)

/-- An all-cost oracle plus admissibility of positive support supplies a zero
avoiding oracle with a penalty whose definition is independent of `α`. -/
theorem oracle_avoids_zero (w : E → ℝ) (α : ℝ) (P : Finset E → Prop)
    (hw : ∀ e, 0 ≤ w e) (hS : P (positiveSupport w))
    (horacle : ∀ d : E → ℝ, (∀ e, 0 ≤ d e) →
      ∃ X : Finset E, P X ∧ (∑ e ∈ X, d e) ≤ α * mwPotential w d)
    (c : E → ℝ) (hc : ∀ e, 0 ≤ c e) :
    ∃ Y : Finset E, P Y ∧ (∀ e ∈ Y, 0 < w e) ∧
      (∑ e ∈ Y, c e) ≤ α * mwPotential w c := by
  obtain ⟨X, hX, hcost⟩ := horacle (penalty (positiveSupport w) c)
    (penalty_nonneg _ _ hc)
  exact ⟨_, choose_preserves_oracle w c α hw hc P hS X hX hcost⟩

end Finite

section Graphs

variable {V : Type*} [Fintype V] [DecidableEq V]

noncomputable def vertexSupport (w : V → ℝ≥0) : Finset V :=
  Finset.univ.filter fun v => 0 < w v

noncomputable def edgeSupport (G : Digraph V) (w : V × V → ℝ≥0) : Finset (V × V) :=
  (graphEdges G).filter fun e => 0 < w e

/-- The fallback meets an internal vertex of every demanded original path. -/
theorem vertexSupport_valid (G : Digraph V) (w : V → ℝ≥0) (D : Set (V × V))
    (hw : IsFractionalCut G w D) : IsIntegralCut G (vertexSupport w) D := by
  classical
  intro s t hst p
  by_contra h
  push Not at h
  have hz : p.weight w = 0 := by
    apply Finset.sum_eq_zero
    intro v hv
    apply le_antisymm _ bot_le
    apply le_of_not_gt
    intro hp
    exact h v hv (Finset.mem_filter.mpr ⟨Finset.mem_univ v, hp⟩)
  have hge := (isFractionalCut_iff G w D).mp hw s t hst p
  rw [hz] at hge
  norm_num at hge

theorem vertexSupport_threshold (G : Digraph V) (w : V → ℝ≥0) :
    IsIntegralCut G (vertexSupport w) (thresholdDemands G w) :=
  vertexSupport_valid G w _ (isFractionalCut_thresholdDemands G w)

/-- Nonedges never occur in this fallback, even if their stored weights are
positive. Endpoints are irrelevant in the edge model. -/
theorem edgeSupport_valid (G : Digraph V) (w : V × V → ℝ≥0) (D : Set (V × V))
    (hw : IsFractionalEdgeCut G w D) : IsIntegralEdgeCut G (edgeSupport G w) D := by
  classical
  intro s t hst p
  by_contra h
  push Not at h
  have hz : p.edgeWeight w = 0 := by
    apply Finset.sum_eq_zero
    intro e he
    apply le_antisymm _ bot_le
    apply le_of_not_gt
    intro hp
    exact h e he (Finset.mem_filter.mpr
      ⟨(mem_graphEdges G e).mpr (p.edge_adj he), hp⟩)
  have hge := (isFractionalEdgeCut_iff G w D).mp hw s t hst p
  rw [hz] at hge
  norm_num at hge

theorem edgeSupport_threshold (G : Digraph V) (w : V × V → ℝ≥0) :
    IsIntegralEdgeCut G (edgeSupport G w) (edgeThresholdDemands G w) :=
  edgeSupport_valid G w _ (isFractionalEdgeCut_thresholdDemands G w)

omit [DecidableEq V] in
theorem edgeSupport_actual (G : Digraph V) (w : V × V → ℝ≥0) :
    edgeSupport G w ⊆ graphEdges G := Finset.filter_subset _ _

/-- A full ordered-pair encoding must zero out nonedges in its proof-level
weights. Their arbitrary stored input weights do not enter the original `W`.
Alternatively the caller can enumerate the subtype of actual original edges. -/
noncomputable def maskedEdgeWeight (G : Digraph V) (w : V × V → ℝ≥0)
    (e : V × V) : ℝ := by
  classical
  exact if G.Adj e.1 e.2 then (w e : ℝ) else 0

omit [DecidableEq V] in
theorem maskedEdgeWeight_support (G : Digraph V) (w : V × V → ℝ≥0) :
    positiveSupport (maskedEdgeWeight G w) = edgeSupport G w := by
  classical
  ext e
  rw [mem_positiveSupport]
  simp only [edgeSupport, Finset.mem_filter, mem_graphEdges, maskedEdgeWeight]
  by_cases he : G.Adj e.1 e.2 <;> simp [he]

omit [DecidableEq V] in
theorem maskedEdgeWeight_total (G : Digraph V) (w : V × V → ℝ≥0) :
    (∑ e, maskedEdgeWeight G w e) = (totalEdgeWeight G w : ℝ) := by
  classical
  rw [totalEdgeWeight, NNReal.coe_sum]
  simp only [maskedEdgeWeight, graphEdges, Finset.sum_filter]

omit [DecidableEq V] in
theorem maskedEdgeWeight_potential (G : Digraph V) (c w : V × V → ℝ≥0) :
    mwPotential (maskedEdgeWeight G w) (fun e => (c e : ℝ)) =
      (weightedEdgeCost G c w : ℝ) := by
  classical
  rw [weightedEdgeCost, NNReal.coe_sum]
  simp only [mwPotential, maskedEdgeWeight, graphEdges,
    Finset.sum_filter, NNReal.coe_mul, mul_ite, mul_zero]

omit [DecidableEq V] in
/-- For any normalized candidate, the finite sum is exactly the graph cost.
Normalization itself preserves validity and cost by the `EdgeModel` lemmas
`edgeCutsPair_filter_actual` and `edgeCutCost_filter_actual`. -/
theorem edge_cost_exact (G : Digraph V) (c : V × V → ℝ≥0)
    (X : Finset (V × V)) (hX : X ⊆ graphEdges G) :
    edgeCutCost G c X = ∑ e ∈ X, c e := by
  classical
  have hf : X.filter (fun e => G.Adj e.1 e.2) = X := by
    apply Finset.filter_eq_self.mpr
    intro e he
    exact (mem_graphEdges G e).mp (hX he)
  simp only [edgeCutCost, hf]

end Graphs

namespace Raw

open RawNonnegativeRational EncodedRoundingInput

abbrev Table (m : ℕ) := Vector Code m
abbrev Mask (m : ℕ) := Vector Bool m

variable {m : ℕ}

def cut (x : Mask m) : Finset (Fin m) := Finset.univ.filter fun e => x[e.val] = true

@[simp] theorem mem_cut (x : Mask m) (e : Fin m) : e ∈ cut x ↔ x[e.val] = true := by
  simp [cut]

noncomputable def value (c : Table m) (e : Fin m) : ℝ := ((c)[e.val].value : ℝ)

def Bounded (c : Table m) (b : ℕ) : Prop := ∀ e : Fin m, (c)[e.val].Bounded b

/-- A literal recursive scan. The natural arithmetic charge is the one in
`Code.addWithCost`; callback and enumeration work is paid in `cutCost`. This
small local routine avoids importing the uncompiled retained-MW draft. -/
def sumCodes (f : Fin m → Code) : List (Fin m) → Code × ℕ
  | [] => (Code.zero, 1)
  | e::es =>
      let r := sumCodes f es
      let s := (f e).addWithCost r.1
      (s.1, r.2 + s.2 + 5)

theorem sumCodes_value (f : Fin m → Code) (es : List (Fin m)) :
    (sumCodes f es).1.value = (es.map fun e => (f e).value).sum := by
  induction es <;> simp [sumCodes, Code.addWithCost, *]

theorem sumCodes_work (f : Fin m → Code) (es : List (Fin m)) :
    (sumCodes f es).2 = 12*es.length + 1 := by
  induction es with
  | nil => rfl
  | cons e es ih =>
      simp only [sumCodes, Code.addWithCost, ih, List.length_cons]
      omega

theorem sumCodes_bounded (f : Fin m → Code) (b : ℕ)
    (hf : ∀ e, (f e).Bounded b) (es : List (Fin m)) :
    (sumCodes f es).1.Bounded (es.length*(b+1)) := by
  induction es with
  | nil => simpa [sumCodes] using Code.bounded_zero
  | cons e es ih =>
      simpa [sumCodes, Code.addWithCost, Nat.add_mul, Nat.mul_add,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using Code.bounded_add (hf e) ih

theorem sum_finRange {A : Type*} [AddCommMonoid A] (f : Fin m → A) :
    ((List.finRange m).map f).sum = ∑ e, f e := by
  rw [← List.sum_toFinset _ (List.nodup_finRange m)]
  have h : (List.finRange m).toFinset = Finset.univ := by ext e; simp
  rw [h]

/-- Sum the mask's actual costs once. The eight extra operations per entry pay
enumeration, array reads, mask test and callback branching. -/
def cutCost (c : Table m) (x : Mask m) : Code × ℕ :=
  let r := sumCodes (fun e => if x[e.val] then (c)[e.val] else Code.zero) (List.finRange m)
  (r.1, r.2 + 8*m + 4)

theorem cutCost_value (c : Table m) (x : Mask m) :
    ((cutCost c x).1.value : ℝ) = ∑ e ∈ cut x, value c e := by
  simp only [cutCost, sumCodes_value, sum_finRange]
  simp only [cut, Finset.sum_filter, NNRat.cast_sum]
  apply Finset.sum_congr rfl
  intro e _
  cases x[e.val] <;> simp [value]

theorem cutCost_work (c : Table m) (x : Mask m) : (cutCost c x).2 = 20*m + 5 := by
  simp [cutCost, sumCodes_work]
  ring

/-- Zero tests inspect the stored numerator, without rational reduction. -/
def support (w : Table m) : Mask m × ℕ :=
  tabulate fun e : Fin m => (decide (w[e.val].num ≠ 0), 6)

@[simp] theorem support_get (w : Table m) (e : Fin m) :
    (support w).1[e.val] = decide (w[e.val].num ≠ 0) := by simp [support]

theorem support_correct (w : Table m) :
    cut (support w).1 = positiveSupport (value w) := by
  classical
  ext e
  simp only [mem_cut, support_get, decide_eq_true_eq, mem_positiveSupport]
  have hp := Code.value_pos w[e.val]
  have hr : 0 < value w e ↔ 0 < w[e.val].value := by
    unfold value
    norm_cast
  rw [hr, hp]
  exact Nat.ne_zero_iff_zero_lt

structure Prepared (m : ℕ) where
  fallback : Mask m
  costs : Table m
  budget : Code
  work : ℕ

/-- Materialize support and costs once. `budget` is the actual current cost of
support, and the penalty is `budget + 1`; no factor or transformed weight is
an executable input. -/
def prepare (w c : Table m) : Prepared m :=
  let s := support w
  let b := cutCost c s.1
  let z := b.1.addWithCost Code.one
  let d := tabulate fun e : Fin m => (if s.1[e.val] then (c)[e.val] else z.1, 6)
  ⟨s.1, d.1, b.1, s.2 + b.2 + z.2 + d.2 + 8⟩

theorem prepare_budget (w c : Table m) :
    ((prepare w c).budget.value : ℝ) = ∑ e ∈ positiveSupport (value w), value c e := by
  simpa only [prepare, support_correct] using cutCost_value c (support w).1

theorem prepare_cost (w c : Table m) (e : Fin m) :
    value (prepare w c).costs e = penalty (positiveSupport (value w)) (value c) e := by
  classical
  have hs : (support w).1[e.val] = true ↔ e ∈ positiveSupport (value w) := by
    rw [← support_correct w, mem_cut]
  have hb := prepare_budget w c
  change ((cutCost c (support w).1).1.value : ℝ) = _ at hb
  change (((tabulate fun j : Fin m =>
    (if (support w).1[j.val] then (c)[j.val] else
      (cutCost c (support w).1).1.add Code.one, 6)).1[e.val]).value : ℝ) = _
  rw [tabulate_get]
  by_cases he : (support w).1[e.val] = true
  · simp [he, penalty, hs.mp he, value]
  · have hn : e ∉ positiveSupport (value w) := fun h => he (hs.mpr h)
    simp [he, penalty, hn, hb]

def prepareWork (m : ℕ) : ℕ := 32*m + 2*arrayBound m + 20

theorem prepare_work (w c : Table m) : (prepare w c).work = prepareWork m := by
  simp [prepare, support, cutCost_work, Code.addWithCost, tabulate_work, prepareWork]
  ring

theorem cutCost_bounded (c : Table m) (x : Mask m) (b : ℕ) (hc : Bounded c b) :
    (cutCost c x).1.Bounded (m*(b+1)) := by
  have h := sumCodes_bounded (fun e : Fin m => if x[e.val] then (c)[e.val] else Code.zero)
    b (by
      intro e
      split
      · exact hc e
      · exact Code.bounded_mono Code.bounded_zero (Nat.zero_le b)) (List.finRange m)
  simpa only [cutCost, List.length_finRange] using h

def queryWidth (m b : ℕ) : ℕ := b + m*(b+1) + 1

theorem prepare_bounded (w c : Table m) (b : ℕ) (hc : Bounded c b) :
    Bounded (prepare w c).costs (queryWidth m b) ∧
      (prepare w c).budget.Bounded (queryWidth m b) := by
  have hb := cutCost_bounded c (support w).1 b hc
  have hz := Code.bounded_add hb Code.bounded_one
  constructor
  · intro e
    change ((tabulate fun j : Fin m =>
      (if (support w).1[j.val] then (c)[j.val] else
        (cutCost c (support w).1).1.add Code.one, 6)).1[e.val]).Bounded _
    rw [tabulate_get]
    split
    · exact Code.bounded_mono (hc e) (by unfold queryWidth; omega)
    · exact Code.bounded_mono hz (by unfold queryWidth; omega)
  · exact Code.bounded_mono hb (by unfold queryWidth; omega)

/-- Both cross-products in the actual comparison have polynomial bit-width in
the number of resources and the current stored cost width. This is a stored
width result, not a substitution of word charges by bit-operation charges. -/
theorem comparison_intermediates (w c : Table m) (x : Mask m) (b : ℕ)
    (hc : Bounded c b) :
    let q := prepare w c
    let a := (cutCost q.costs x).1
    let K := m*(queryWidth m b+1) + queryWidth m b
    a.num*q.budget.den ≤ 2^K ∧ q.budget.num*a.den ≤ 2^K := by
  have hq := prepare_bounded w c b hc
  exact Code.comparison_intermediates (cutCost_bounded _ x _ hq.1) hq.2

/-- The oracle work is retained in both branches. An explicit failure returns
support; a successful return is compared using its actual penalized cost. -/
def select (q : Prepared m) (o : Option (Mask m) × ℕ) : Mask m × ℕ :=
  match o.1 with
  | none => (q.fallback, o.2 + 4)
  | some x =>
      let c := cutCost q.costs x
      let b := c.1.leWithCost q.budget
      (if b.1 then x else q.fallback, o.2 + c.2 + b.2 + 8)

@[simp] theorem select_none (q : Prepared m) (work : ℕ) :
    (select q (none, work)).1 = q.fallback := rfl

theorem select_work (q : Prepared m) (o : Option (Mask m) × ℕ) :
    (select q o).2 ≤ o.2 + 20*m + 17 := by
  cases h : o.1 with
  | none => simp only [select, h]; omega
  | some x => simp only [select, h, cutCost_work, Code.leWithCost]; omega

/-- This exact refinement links the executable comparison to the finite
selector; it does not assume an encoded value of `α`. -/
theorem select_some_refines (w c : Table m) (x : Mask m) (work : ℕ) :
    cut (select (prepare w c) (some x, work)).1 =
      choose (positiveSupport (value w)) (value c) (cut x) := by
  classical
  let q := prepare w c
  have hf : cut q.fallback = positiveSupport (value w) := support_correct w
  have hb : (cutCost q.costs x).1.le q.budget = true ↔
      (∑ e ∈ cut x, penalty (positiveSupport (value w)) (value c) e) ≤
        ∑ e ∈ positiveSupport (value w), value c e := by
    rw [Code.le_eq_true]
    have he : (cutCost q.costs x).1.value ≤ q.budget.value ↔
        ((cutCost q.costs x).1.value : ℝ) ≤
          (q.budget.value : ℝ) := by norm_cast
    rw [he, cutCost_value, prepare_budget]
    simp only [q, prepare_cost]
  change cut (if (cutCost q.costs x).1.le q.budget then x else q.fallback) = _
  unfold choose
  by_cases h : (cutCost q.costs x).1.le q.budget = true
  · rw [ite_eq_left h, ite_eq_left (hb.mp h)]
  · have hn := fun hle => h (hb.mpr hle)
    rw [ite_eq_right h, ite_eq_right hn]
    exact hf

/-- Validity and zero avoidance hold even on an explicitly signaled failure.
An invalid `some` result is not magically certified by the budget comparison. -/
theorem select_valid_avoids (w c : Table m) (o : Option (Mask m) × ℕ)
    (P : Finset (Fin m) → Prop) (hS : P (positiveSupport (value w)))
    (hvalid : ∀ x, o.1 = some x → P (cut x)) :
    P (cut (select (prepare w c) o).1) ∧
      ∀ e ∈ cut (select (prepare w c) o).1, 0 < value w e := by
  have hc : ∀ e, 0 ≤ value c e := fun e => by unfold value; positivity
  rcases o with ⟨o, work⟩
  cases o with
  | none =>
      change P (cut (support w).1) ∧ ∀ e ∈ cut (support w).1, 0 < value w e
      rw [support_correct]
      exact ⟨hS, fun e he => (mem_positiveSupport _ _).mp he⟩
  | some x =>
      rw [select_some_refines]
      exact ⟨choose_valid _ _ _ P hS (hvalid x rfl),
        fun e he => (mem_positiveSupport _ _).mp (choose_subset _ _ hc _ he)⟩

/-- The original real factor is used only in the proof-level oracle contract.
The executable output satisfies that same factor, with the original weights. -/
theorem select_preserves_factor (w c : Table m) (x : Mask m) (work : ℕ) (α : ℝ)
    (hcost : (∑ e ∈ cut x, value (prepare w c).costs e) ≤
      α * mwPotential (value w) (value (prepare w c).costs)) :
    (∑ e ∈ cut (select (prepare w c) (some x, work)).1, value c e) ≤
      α * mwPotential (value w) (value c) := by
  have hw : ∀ e, 0 ≤ value w e := fun e => by unfold value; positivity
  have hc : ∀ e, 0 ≤ value c e := fun e => by unfold value; positivity
  have he : value (prepare w c).costs = penalty (positiveSupport (value w)) (value c) :=
    funext (prepare_cost w c)
  rw [he, penalty_potential _ _ hw] at hcost
  rw [select_some_refines]
  exact (choose_cost_le _ _ hc _).trans hcost

/-- One actual oracle call at the retained penalized cost table. -/
def run (w c : Table m) (oracle : Table m → Option (Mask m) × ℕ) : Mask m × ℕ :=
  let q := prepare w c
  let o := oracle q.costs
  let r := select q o
  (r.1, q.work + r.2 + 4)

theorem run_work (w c : Table m) (oracle : Table m → Option (Mask m) × ℕ) :
    (run w c oracle).2 ≤
      (oracle (prepare w c).costs).2 + prepareWork m + 20*m + 21 := by
  have hs := select_work (prepare w c) (oracle (prepare w c).costs)
  simp only [run, prepare_work]
  omega

theorem run_valid_avoids (w c : Table m) (oracle : Table m → Option (Mask m) × ℕ)
    (P : Finset (Fin m) → Prop) (hS : P (positiveSupport (value w)))
    (hvalid : ∀ x, (oracle (prepare w c).costs).1 = some x → P (cut x)) :
    P (cut (run w c oracle).1) ∧
      ∀ e ∈ cut (run w c oracle).1, 0 < value w e :=
  select_valid_avoids w c _ P hS hvalid

theorem run_preserves_factor (w c : Table m) (oracle : Table m → Option (Mask m) × ℕ)
    (x : Mask m) (α : ℝ) (hx : (oracle (prepare w c).costs).1 = some x)
    (hcost : (∑ e ∈ cut x, value (prepare w c).costs e) ≤
      α * mwPotential (value w) (value (prepare w c).costs)) :
    (∑ e ∈ cut (run w c oracle).1, value c e) ≤
      α * mwPotential (value w) (value c) := by
  rcases ho : oracle (prepare w c).costs with ⟨result, work⟩
  have hr : result = some x := by simpa only [ho] using hx
  subst result
  simpa only [run, ho] using select_preserves_factor w c x work α hcost

end Raw

end DirectedFlowCutGap.ZeroAvoidingSelector
