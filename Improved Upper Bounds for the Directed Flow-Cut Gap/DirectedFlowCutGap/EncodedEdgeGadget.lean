import DirectedFlowCutGap.EncodedEdgeLabels
import DirectedFlowCutGap.EdgeToVertexReduction
import DirectedFlowCutGap.CandidateEnumeration
import DirectedFlowCutGap.EncodedUnitCostReplication
import DirectedFlowCutGap.FractionalCoverRawCore

/-!
# The retained array graph for the dyadic edge gadget

Input label comparisons use stored rational fields. The node enumeration
retains both terminal ports and precisely the labels incident to actual
edges, in a fixed order. The adjacency, weight and cost arrays all use
that same enumeration.
-/

namespace DirectedFlowCutGap.EncodedEdgeGadget

open scoped NNReal
open RawNonnegativeRational

abbrev Pair (n : ℕ) := Fin n × Fin n
abbrev Labels (n : ℕ) := Vector (Vector (DyadicEdgeWeights.Label n) n) n
abbrev RawNode (n : ℕ) := EdgeToVertex.RawNode (Fin n) (DyadicEdgeWeights.Label n)

structure Input (n : ℕ) where
  adjacency : Vector (Vector Bool n) n
  weights : Vector (Vector Code n) n
  costs : Vector (Vector Code n) n

def Input.graph {n : ℕ} (D : Input n) : Digraph (Fin n) where
  Adj u v := D.adjacency[u.val][v.val] = true

noncomputable def Input.weight {n : ℕ} (D : Input n) (e : Pair n) : ℝ≥0 :=
  D.weights[e.1.val][e.2.val].realValue

noncomputable def Input.cost {n : ℕ} (D : Input n) (e : Pair n) : ℝ≥0 :=
  D.costs[e.1.val][e.2.val].realValue

def labelTable {n : ℕ} (D : Input n) : Labels n :=
  Vector.ofFn fun u => Vector.ofFn fun v => EncodedEdgeLabels.label n D.weights[u.val][v.val]

def labelAt {n : ℕ} (labels : Labels n) (e : Pair n) : DyadicEdgeWeights.Label n :=
  labels[e.1.val][e.2.val]

theorem labelAt_table {n : ℕ} (D : Input n) (e : Pair n) :
    labelAt (labelTable D) e = DyadicEdgeWeights.round n (D.weight e) := by
  simp only [labelAt, labelTable, Vector.getElem_ofFn, Input.weight, EncodedEdgeLabels.label_value]

abbrev Node {n : ℕ} (D : Input n) (labels : Labels n) := EdgeToVertex.Node D.graph (labelAt labels)

private def finiteLabels (n : ℕ) : CandidateEnumeration.Built (DyadicEdgeWeights.Label n) :=
  CandidateEnumeration.pack (none :: (List.finRange (DyadicEdgeWeights.depth n + 1)).map some)
    (List.nodup_cons.mpr ⟨by simp, (List.nodup_finRange _).map (Option.some_injective _)⟩)
    (by intro x; cases x <;> simp)
    (16 * (DyadicEdgeWeights.depth n + 2) + 8)

private def rawEnumeration (n : ℕ) : CandidateEnumeration.Built (RawNode n) :=
  let vertices := CandidateEnumeration.fin n
  let sides := CandidateEnumeration.bool
  CandidateEnumeration.sum (CandidateEnumeration.prod vertices sides)
    (CandidateEnumeration.prod vertices (CandidateEnumeration.prod sides (finiteLabels n)))

def edges {n : ℕ} (D : Input n) : List (Pair n) :=
  ((List.finRange n).product (List.finRange n)).filter fun e => D.adjacency[e.1.val][e.2.val]

theorem edges_mem {n : ℕ} (D : Input n) (e : Pair n) :
    e ∈ edges D ↔ e ∈ graphEdges D.graph := by
  rcases e with ⟨u, v⟩
  simp [edges, Input.graph]

theorem edges_nodup {n : ℕ} (D : Input n) : (edges D).Nodup :=
  (List.Nodup.product (List.nodup_finRange _) (List.nodup_finRange _)).filter _

private def active {n : ℕ} (es : List (Pair n)) (labels : Labels n) : RawNode n → Bool
  | .inl _ => true
  | .inr x => es.any (fun e =>
      decide (Sum.inr x = EdgeToVertex.right (labelAt labels) e ∨
        Sum.inr x = EdgeToVertex.left (labelAt labels) e))

private theorem active_iff {n : ℕ} (D : Input n) (labels : Labels n) (x : RawNode n) :
    active (edges D) labels x = true ↔ EdgeToVertex.Active D.graph (labelAt labels) x := by
  cases x with
  | inl x =>
    simp only [active, true_iff]
    exact Or.inl ⟨x.1, x.2, rfl⟩
  | inr x =>
    simp only [active, List.any_eq_true, decide_eq_true_eq, EdgeToVertex.Active,
      Sum.inr_ne_inl, exists_false, false_or, edges_mem]

def nodes {n : ℕ} (D : Input n) (labels : Labels n) : List (Node D labels) :=
  let raw := (rawEnumeration n).enumeration.vertices.filter (active (edges D) labels)
  raw.attach.map fun x => ⟨x.1, (active_iff D labels x.1).mp (List.mem_filter.mp x.2).2⟩

theorem nodes_nodup {n : ℕ} (D : Input n) (labels : Labels n) : (nodes D labels).Nodup := by
  unfold nodes
  apply List.Nodup.map
  · intro a b h
    exact Subtype.ext (congrArg (fun z : Node D labels => z.val) h)
  · exact List.nodup_attach.mpr ((rawEnumeration n).enumeration.nodup.filter _)

theorem nodes_mem {n : ℕ} (D : Input n) (labels : Labels n) (x : Node D labels) :
    x ∈ nodes D labels := by
  let raw := (rawEnumeration n).enumeration.vertices.filter (active (edges D) labels)
  have hm : x.val ∈ raw := List.mem_filter.mpr
    ⟨(rawEnumeration n).enumeration.complete x.val, (active_iff D labels x.val).mpr x.property⟩
  exact List.mem_map.mpr ⟨⟨x.val, hm⟩, List.mem_attach _ _, Subtype.ext rfl⟩

private def adjacent {n : ℕ} (D : Input n) (labels : Labels n) : RawNode n → RawNode n → Bool
  | .inl (u, true), .inl (v, false) => decide (u = v)
  | .inl (u, true), .inr (v, true, _) => decide (u = v)
  | .inr (u, false, _), .inl (v, false) => decide (u = v)
  | .inr (u, false, _), .inr (v, true, _) => decide (u = v)
  | .inr (u, true, i), .inr (v, false, j) =>
    D.adjacency[u.val][v.val] && decide (labelAt labels (u, v) = i ∧ labelAt labels (u, v) = j)
  | _, _ => false

private theorem adjacent_iff {n : ℕ} (D : Input n) (labels : Labels n) (x y : RawNode n) :
    adjacent D labels x y = true ↔ EdgeToVertex.RawAdj D.graph (labelAt labels) x y := by
  rcases x with ⟨u, b⟩ | ⟨u, b, i⟩ <;> rcases y with ⟨v, c⟩ | ⟨v, c, j⟩ <;>
    cases b <;> cases c <;> simp [adjacent, EdgeToVertex.RawAdj, Input.graph]

private def nodeWeight {n : ℕ} : RawNode n → Code
  | .inl _ => Code.zero
  | .inr (_, _, i) => EncodedEdgeLabels.valueCode i

private def edgeCharge {n : ℕ} (D : Input n) (labels : Labels n) (x : RawNode n) (e : Pair n) : Code :=
  let cost := D.costs[e.1.val][e.2.val]
  (if x = EdgeToVertex.right (labelAt labels) e then cost else Code.zero).add
    (if x = EdgeToVertex.left (labelAt labels) e then cost else Code.zero)

structure Prepared {n : ℕ} (D : Input n) where
  size : ℕ
  labels : Labels n
  vertices : Vector (Node D labels) size
  data : EncodedUnitCostReplication.Input size

def build {n : ℕ} (D : Input n) : Prepared D :=
  let l := labelTable D
  let es := edges D
  let vs := nodes D l
  let m := vs.length
  let v : Vector (Node D l) m := ⟨vs.toArray, by simp [m]⟩
  ⟨m, l, v,
    { adjacency := Vector.ofFn fun x => Vector.ofFn fun y => adjacent D l v[x.val].val v[y.val].val
      weights := Vector.ofFn fun x => nodeWeight v[x.val].val
      costs := Vector.ofFn fun x =>
        FractionalCoverRawCore.sumCodes (es.map (edgeCharge D l v[x.val].val)) }⟩

def indexEquiv {n : ℕ} (D : Input n) : Fin (build D).size ≃ Node D (labelTable D) :=
  List.Nodup.getEquivOfForallMemList _ (nodes_nodup D (labelTable D)) (nodes_mem D (labelTable D))

@[simp] theorem indexEquiv_apply {n : ℕ} (D : Input n) (i : Fin (build D).size) :
    indexEquiv D i = (build D).vertices[i.val] := rfl

theorem build_adj {n : ℕ} (D : Input n) (i j : Fin (build D).size) :
    (build D).data.graph.Adj i j ↔
      (EdgeToVertex.graph D.graph (labelAt (labelTable D))).Adj (indexEquiv D i) (indexEquiv D j) := by
  have h : (build D).data.graph.Adj i j ↔ adjacent D (labelTable D)
      (build D).vertices[i.val].val (build D).vertices[j.val].val = true := by
    simp only [EncodedUnitCostReplication.Input.graph, build, Vector.getElem_ofFn]
  rw [← indexEquiv_apply D i, ← indexEquiv_apply D j] at h
  exact h.trans (adjacent_iff D (labelTable D) (indexEquiv D i).val (indexEquiv D j).val)

theorem build_weight {n : ℕ} (D : Input n) (i : Fin (build D).size) :
    (build D).data.weight i = EdgeToVertex.weight D.graph (labelAt (labelTable D))
      (DyadicEdgeWeights.value n) (indexEquiv D i) := by
  have h : EdgeToVertex.Active D.graph (labelAt (labelTable D)) (indexEquiv D i).val :=
    (indexEquiv D i).property
  unfold EdgeToVertex.weight
  rw [EdgeToVertex.rawWeight.eq_def, ite_eq_left h]
  simp only [EncodedUnitCostReplication.Input.weight, build, Vector.getElem_ofFn]
  change (nodeWeight (indexEquiv D i).val).realValue = _
  cases (indexEquiv D i).val with
  | inl x => simp [nodeWeight, Code.realValue]
  | inr x => exact EncodedEdgeLabels.valueCode_value x.2.2

private theorem sumCodes_value (xs : List Code) :
    (FractionalCoverRawCore.sumCodes xs).realValue = (xs.map Code.realValue).sum := by
  induction xs with
  | nil => simp [FractionalCoverRawCore.sumCodes, Code.realValue]
  | cons q qs ih => simp [FractionalCoverRawCore.sumCodes, Code.realValue, ← ih]

theorem build_cost {n : ℕ} (D : Input n) (i : Fin (build D).size) :
    (build D).data.cost i = EdgeToVertex.cost D.graph (labelAt (labelTable D)) D.cost (indexEquiv D i) := by
  have he : (edges D).toFinset = graphEdges D.graph := by
    ext e
    simp [edges_mem]
  unfold EdgeToVertex.cost EdgeToVertex.rawCost
  simp only [EncodedUnitCostReplication.Input.cost, build, Vector.getElem_ofFn]
  change (FractionalCoverRawCore.sumCodes
      ((edges D).map (edgeCharge D (labelTable D) (indexEquiv D i).val))).realValue = _
  rw [sumCodes_value, List.map_map, ← List.sum_toFinset _ (edges_nodup D), he]
  apply Finset.sum_congr rfl
  intro e _
  have hi (p : Prop) [Decidable p] (c : Code) :
      (if p then c else Code.zero).realValue = if p then c.realValue else 0 := by
    by_cases hp : p <;> simp [hp, Code.realValue]
  have ha (a b : Code) : (a.add b).realValue = a.realValue + b.realValue := by
    simp [Code.realValue]
  simp only [Function.comp_apply, edgeCharge, ha, hi, Input.cost]
  split_ifs <;> first | rfl | contradiction

theorem build_size_le {n : ℕ} (D : Input n) :
    (build D).size ≤ 2 * n * (Nat.log2 n + 4) := by
  classical
  rw [← Fintype.card_fin (n := (build D).size), Fintype.card_congr (indexEquiv D)]
  simpa only [Fintype.card_fin, DyadicEdgeWeights.card_label_log2, Nat.add_assoc] using
    EdgeToVertex.card_node_le D.graph (labelAt (labelTable D))

theorem build_totalWeight_le {n : ℕ} (D : Input n) :
    totalWeight (build D).data.weight ≤ 4 * totalEdgeWeight D.graph D.weight := by
  classical
  let labels := labelAt (labelTable D)
  let weights := DyadicEdgeWeights.value n
  have h : totalEdgeWeight D.graph (weights ∘ labels) ≤ 2 * totalEdgeWeight D.graph D.weight := by
    unfold totalEdgeWeight
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro e _
    simpa only [Function.comp_apply, labels, weights, labelAt_table] using
      DyadicEdgeWeights.value_round_le_twice n (D.weight e)
  calc
    _ = totalWeight (EdgeToVertex.weight D.graph labels weights) := by
      simp only [totalWeight, build_weight]
      exact (indexEquiv D).sum_comp _
    _ ≤ 2 * totalEdgeWeight D.graph (weights ∘ labels) := EdgeToVertex.totalWeight_le ..
    _ ≤ 4 * totalEdgeWeight D.graph D.weight := by linarith

theorem build_weightedCost_le {n : ℕ} (D : Input n) :
    weightedCost (build D).data.cost (build D).data.weight ≤
      4 * weightedEdgeCost D.graph D.cost D.weight := by
  classical
  let labels := labelAt (labelTable D)
  let weights := DyadicEdgeWeights.value n
  have h : weightedEdgeCost D.graph D.cost (weights ∘ labels) ≤
      2 * weightedEdgeCost D.graph D.cost D.weight := by
    unfold weightedEdgeCost
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro e _
    calc
      D.cost e * (weights ∘ labels) e ≤ D.cost e * (2 * D.weight e) := by
        apply mul_le_mul_of_nonneg_left _ zero_le
        simpa only [Function.comp_apply, labels, weights, labelAt_table] using
          DyadicEdgeWeights.value_round_le_twice n (D.weight e)
      _ = _ := by ring
  have hh : weightedCost (build D).data.cost (build D).data.weight =
      weightedCost (EdgeToVertex.cost D.graph labels D.cost) (EdgeToVertex.weight D.graph labels weights) := by
    simp only [weightedCost, build_cost, build_weight]
    exact (indexEquiv D).sum_comp (fun v : Node D (labelTable D) =>
      EdgeToVertex.cost D.graph labels D.cost v * EdgeToVertex.weight D.graph labels weights v)
  rw [hh, EdgeToVertex.weightedCost_eq]
  linarith

theorem threshold_transfer {n : ℕ} (D : Input n) {s t : Fin n}
    (h : 1 ≤ edgeDistance D.graph D.weight s t) :
    1 ≤ vertexDistance (EdgeToVertex.graph D.graph (labelAt (labelTable D)))
      (EdgeToVertex.weight D.graph (labelAt (labelTable D)) (DyadicEdgeWeights.value n))
      (EdgeToVertex.source D.graph (labelAt (labelTable D)) s)
      (EdgeToVertex.target D.graph (labelAt (labelTable D)) t) := by
  have hn : 0 < n := Nat.zero_lt_of_lt s.isLt
  apply EdgeToVertex.threshold_transfer _ _ _ D.weight _ _ h
  · intro e he
    simpa only [labelAt_table, Fintype.card_fin, DyadicEdgeWeights.cutoff] using
      DyadicEdgeWeights.le_value_round_add hn he
  · intro e he
    rw [labelAt_table, DyadicEdgeWeights.value_round_of_one_le hn he]

end DirectedFlowCutGap.EncodedEdgeGadget
