import DirectedFlowCutGap.BinaryFilter
import DirectedFlowCutGap.BinaryVectorAccess
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
  let labels := finiteLabels n
  let ports := CandidateEnumeration.prod vertices sides
  let sideLabels := CandidateEnumeration.prod sides labels
  let labeled := CandidateEnumeration.prod vertices sideLabels
  let result := CandidateEnumeration.sum ports labeled
  { result with work := vertices.work+sides.work+labels.work+ports.work+sideLabels.work+labeled.work+result.work+8 }

private def filterWithCost {A : Type*} (test : A → Bool × ℕ) (xs : List A) : List A × ℕ :=
  BinaryFilter.reference test [] 0 xs

private theorem filterWithCost_value {A : Type*} (test : A → Bool × ℕ) (xs : List A) :
    (filterWithCost test xs).1=xs.filter (fun x => (test x).1) := by
  have loop (kept : List A) (paid : ℕ) (xs : List A) :
      (BinaryFilter.reference test kept paid xs).1=kept.reverse++xs.filter (fun x => (test x).1) := by
    induction xs generalizing kept paid with
    | nil => simp [BinaryFilter.reference]
    | cons x xs ih =>
      simp only [BinaryFilter.reference,List.filter_cons,ih]
      split <;> simp_all
  simpa only [filterWithCost,List.reverse_nil,List.nil_append] using loop [] 0 xs

private theorem filterWithCost_paid {A : Type*} (test : A → Bool × ℕ) (xs : List A) (cap : ℕ)
    (cost : ∀ x, (test x).2 ≤ cap) : (filterWithCost test xs).2 ≤ xs.length*(cap+8)+1 := by
  have loop (kept : List A) (paid : ℕ) (xs : List A) :
      (BinaryFilter.reference test kept paid xs).2 ≤ paid+xs.length*(cap+8)+1 := by
    induction xs generalizing kept paid with
    | nil => simp [BinaryFilter.reference]
    | cons x xs ih =>
      have head := cost x
      simp only [BinaryFilter.reference,List.length_cons,Nat.add_mul,Nat.one_mul]
      exact (ih _ _).trans (by omega)
  simpa only [filterWithCost,Nat.zero_add] using loop [] 0 xs

def edges {n : ℕ} (D : Input n) : List (Pair n) :=
  ((List.finRange n).product (List.finRange n)).filter fun e => D.adjacency[e.1.val][e.2.val]

private def edgeCandidate {n : ℕ} (D : Input n) (e : Pair n) : (Bool × ℕ) × ℕ :=
  let live := BinaryVectorAccess.readMatrix D.adjacency e.1 e.2
  ((live.1,8),live.2)

def edgesWithControl {n : ℕ} (D : Input n) : (List (Pair n) × ℕ) × ℕ :=
  let vertices := CandidateEnumeration.fin n
  let pairs := CandidateEnumeration.prod vertices vertices
  let out := BinaryFilter.run (edgeCandidate D) pairs.enumeration.vertices
  ((out.1.1,vertices.work+pairs.work+out.1.2+8),out.2)

def edgesWithCost {n : ℕ} (D : Input n) : List (Pair n) × ℕ := (edgesWithControl D).1

theorem edges_reference {n : ℕ} (D : Input n) : edgesWithCost D =
    let vertices := CandidateEnumeration.fin n
    let pairs := CandidateEnumeration.prod vertices vertices
    let out := filterWithCost (fun e => (D.adjacency[e.1.val][e.2.val],8)) pairs.enumeration.vertices
    (out.1,vertices.work+pairs.work+out.2+8) := by
  simp only [edgesWithCost,edgesWithControl,BinaryFilter.run_reference,edgeCandidate,
    BinaryVectorAccess.readMatrix_value,filterWithCost]

def edgesControlBudget {R : Type*} [Semiring R] (n : R) : R :=
  BinaryFilter.controlBudget (n*n) 8 (2*BinaryVectorAccess.budget n)

theorem edges_control_paid {n : ℕ} (D : Input n) : (edgesWithControl D).2 ≤ edgesControlBudget n := by
  let vertices := CandidateEnumeration.fin n
  let pairs := CandidateEnumeration.prod vertices vertices
  have len : pairs.enumeration.vertices.length=n*n := by
    simp only [pairs,vertices,CandidateEnumeration.prod_length,CandidateEnumeration.fin_length]
  have width : n.size≤n := Nat.size_le.mpr Nat.lt_two_pow_self
  have paid := BinaryFilter.run_paid (edgeCandidate D) pairs.enumeration.vertices 8 (2*BinaryVectorAccess.budget n)
    (fun e _ => ⟨le_rfl,BinaryVectorAccess.readMatrix_paid D.adjacency e.1 e.2 width width⟩)
  rw [len] at paid
  exact paid

@[simp] theorem edgesWithCost_value {n : ℕ} (D : Input n) : (edgesWithCost D).1=edges D := by
  simp only [edges_reference,filterWithCost_value,CandidateEnumeration.prod_vertices,CandidateEnumeration.fin_vertices]
  rfl

def edgesBudget {R : Type*} [Semiring R] (n : R) : R := 48*(n+1)^2

theorem edgesWithCost_paid {n : ℕ} (D : Input n) : (edgesWithCost D).2 ≤ edgesBudget n := by
  let vertices := CandidateEnumeration.fin n
  let pairs := CandidateEnumeration.prod vertices vertices
  have paid := filterWithCost_paid (fun e : Pair n => (D.adjacency[e.1.val][e.2.val],8))
    pairs.enumeration.vertices 8 (fun _ => le_rfl)
  rw [edges_reference]
  change vertices.work+pairs.work+(filterWithCost _ _).2+8 ≤ _
  simp only [vertices,pairs,CandidateEnumeration.prod_length,CandidateEnumeration.fin_length,Nat.reduceAdd] at paid
  simp only [vertices,pairs,CandidateEnumeration.prod_work,CandidateEnumeration.fin_work,
    CandidateEnumeration.fin_length,edgesBudget]
  nlinarith only [paid]

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

private def refineNodes {n : ℕ} (D : Input n) (labels : Labels n) (xs : List (RawNode n))
    (h : ∀ x ∈ xs, EdgeToVertex.Active D.graph (labelAt labels) x) : List (Node D labels) :=
  xs.attach.map fun x => ⟨x.1,h x.1 x.2⟩

def nodes {n : ℕ} (D : Input n) (labels : Labels n) : List (Node D labels) :=
  let raw := (rawEnumeration n).enumeration.vertices.filter (active (edges D) labels)
  refineNodes D labels raw (fun x h => (active_iff D labels x).mp (List.mem_filter.mp h).2)

theorem nodes_nodup {n : ℕ} (D : Input n) (labels : Labels n) : (nodes D labels).Nodup := by
  unfold nodes refineNodes
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

def nodeWeight {n : ℕ} : RawNode n → Code
  | .inl _ => Code.zero
  | .inr (_, _, i) => EncodedEdgeLabels.valueCode i

def edgeCharge {n : ℕ} (D : Input n) (labels : Labels n) (x : RawNode n) (e : Pair n) : Code :=
  let cost := D.costs[e.1.val][e.2.val]
  (if x = EdgeToVertex.right (labelAt labels) e then cost else Code.zero).add
    (if x = EdgeToVertex.left (labelAt labels) e then cost else Code.zero)

structure Prepared {n : ℕ} (D : Input n) where
  size : ℕ
  labels : Labels n
  vertices : Vector (Node D labels) size
  data : EncodedUnitCostReplication.Input size

def assemble {n m : ℕ} (D : Input n) (l : Labels n)
    (v : Vector (Node D l) m) (weights costs : Vector Code m) : Prepared D :=
  ⟨m, l, v,
    { adjacency := Vector.ofFn fun x => Vector.ofFn fun y => adjacent D l v[x.val].val v[y.val].val
      weights := weights
      costs := costs }⟩

def nodeVector {n : ℕ} (D : Input n) (l : Labels n) : Vector (Node D l) (nodes D l).length :=
  ⟨(nodes D l).toArray, by simp⟩

private theorem filter_active_value {n : ℕ} (D : Input n) (l : Labels n) (test : RawNode n → Bool × ℕ)
    (exactTest : ∀ x, (test x).1=true ↔ EdgeToVertex.Active D.graph (labelAt l) x) :
    (filterWithCost test (rawEnumeration n).enumeration.vertices).1=
      (rawEnumeration n).enumeration.vertices.filter (active (edges D) l) := by
  rw [filterWithCost_value]
  congr 1
  funext x
  exact Bool.eq_iff_iff.mpr ((exactTest x).trans (active_iff D l x).symm)

private def selectedNodesFrom {n : ℕ} (D : Input n) (l : Labels n) (test : RawNode n → Bool × ℕ)
    (exactTest : ∀ x, (test x).1=true ↔ EdgeToVertex.Active D.graph (labelAt l) x)
    (out : List (RawNode n) × ℕ)
    (same : out.1=((rawEnumeration n).enumeration.vertices.filter fun x => (test x).1)) : List (Node D l) × ℕ :=
  let found := refineNodes D l out.1 (by
    intro x mem
    rw [same] at mem
    exact (exactTest x).mp (List.mem_filter.mp mem).2)
  (found,(rawEnumeration n).work+out.2+16*found.length+4)

private def selectedNodes {n : ℕ} (D : Input n) (l : Labels n) (test : RawNode n → Bool × ℕ)
    (exactTest : ∀ x, (test x).1=true ↔ EdgeToVertex.Active D.graph (labelAt l) x) : List (Node D l) × ℕ :=
  selectedNodesFrom D l test exactTest (filterWithCost test (rawEnumeration n).enumeration.vertices)
    (filterWithCost_value test (rawEnumeration n).enumeration.vertices)

private def selectedNodesWithControl {n : ℕ} (D : Input n) (l : Labels n) (test : RawNode n → (Bool × ℕ) × ℕ)
    (exactTest : ∀ x, (test x).1.1=true ↔ EdgeToVertex.Active D.graph (labelAt l) x) :
    (List (Node D l) × ℕ) × ℕ :=
  let candidates := (rawEnumeration n).enumeration.vertices
  let out := BinaryFilter.run test candidates
  let found := selectedNodesFrom D l (fun x => (test x).1) exactTest out.1 (by
    rw [BinaryFilter.run_reference]
    exact filterWithCost_value _ _)
  (found,out.2)

private theorem selectedNodes_reference {n : ℕ} (D : Input n) (l : Labels n) (test : RawNode n → (Bool × ℕ) × ℕ)
    (exactTest : ∀ x, (test x).1.1=true ↔ EdgeToVertex.Active D.graph (labelAt l) x) :
    (selectedNodesWithControl D l test exactTest).1=selectedNodes D l (fun x => (test x).1) exactTest := by
  let candidates := (rawEnumeration n).enumeration.vertices
  have reference : (BinaryFilter.run test candidates).1=filterWithCost (fun x => (test x).1) candidates :=
    BinaryFilter.run_reference _ _
  unfold selectedNodesWithControl selectedNodes
  dsimp only
  have changeFilter (a b : List (RawNode n) × ℕ) (ha : a.1=candidates.filter (fun x => (test x).1.1))
      (hb : b.1=candidates.filter (fun x => (test x).1.1)) (h : a=b) :
      selectedNodesFrom D l (fun x => (test x).1) exactTest a ha =
        selectedNodesFrom D l (fun x => (test x).1) exactTest b hb := by
    subst b
    rfl
  exact changeFilter _ _ _ _ reference

private theorem selectedNodes_value {n : ℕ} (D : Input n) (l : Labels n) (test : RawNode n → Bool × ℕ)
    (exactTest : ∀ x, (test x).1=true ↔ EdgeToVertex.Active D.graph (labelAt l) x) :
    (selectedNodes D l test exactTest).1=nodes D l := by
  have same (xs ys : List (RawNode n)) (hx : ∀ x ∈ xs, EdgeToVertex.Active D.graph (labelAt l) x)
      (hy : ∀ y ∈ ys, EdgeToVertex.Active D.graph (labelAt l) y) (h : xs=ys) :
      refineNodes D l xs hx=refineNodes D l ys hy := by subst ys; rfl
  unfold selectedNodes selectedNodesFrom nodes
  dsimp only
  apply same
  exact filter_active_value D l test exactTest

def nodeVectorWithCost {n : ℕ} (D : Input n) (l : Labels n) (test : RawNode n → Bool × ℕ)
    (exactTest : ∀ x, (test x).1=true ↔ EdgeToVertex.Active D.graph (labelAt l) x) :
    Vector (Node D l) (nodes D l).length × ℕ :=
  let r := selectedNodes D l test exactTest
  (⟨r.1.toArray,by simp only [r,List.size_toArray,selectedNodes_value]⟩,r.2)

@[simp] theorem nodeVectorWithCost_value {n : ℕ} (D : Input n) (l : Labels n) (test : RawNode n → Bool × ℕ)
    (exactTest : ∀ x, (test x).1=true ↔ EdgeToVertex.Active D.graph (labelAt l) x) :
    (nodeVectorWithCost D l test exactTest).1=nodeVector D l :=
  Vector.toArray_injective (congrArg List.toArray (selectedNodes_value D l test exactTest))

def nodeVectorWithControl {n : ℕ} (D : Input n) (l : Labels n) (test : RawNode n → (Bool × ℕ) × ℕ)
    (exactTest : ∀ x, (test x).1.1=true ↔ EdgeToVertex.Active D.graph (labelAt l) x) :
    (Vector (Node D l) (nodes D l).length × ℕ) × ℕ :=
  let r := selectedNodesWithControl D l test exactTest
  let vector : Vector (Node D l) (nodes D l).length := ⟨r.1.1.toArray,by
    simp only [r,List.size_toArray,selectedNodes_reference,selectedNodes_value]⟩
  ((vector,r.1.2),r.2)

theorem nodeVector_reference {n : ℕ} (D : Input n) (l : Labels n) (test : RawNode n → (Bool × ℕ) × ℕ)
    (exactTest : ∀ x, (test x).1.1=true ↔ EdgeToVertex.Active D.graph (labelAt l) x) :
    (nodeVectorWithControl D l test exactTest).1 = nodeVectorWithCost D l (fun x => (test x).1) exactTest := by
  have reference := selectedNodes_reference D l test exactTest
  apply Prod.ext
  · apply Vector.toArray_injective
    exact congrArg (fun (r : List (Node D l) × ℕ) => r.1.toArray) reference
  · exact congrArg (fun (r : List (Node D l) × ℕ) => r.2) reference

private theorem rawEnumeration_length (n : ℕ) : (rawEnumeration n).enumeration.vertices.length ≤ 2*n*(n+4) := by
  have hdepth : DyadicEdgeWeights.depth n ≤ n+1 := Nat.add_le_add_right (Nat.log_le_self 2 n) 1
  have hlabels : (finiteLabels n).enumeration.vertices.length = DyadicEdgeWeights.depth n+2 := by
    simp only [finiteLabels,CandidateEnumeration.pack_vertices,List.length_cons,List.length_map,List.length_finRange]
  simp only [rawEnumeration,CandidateEnumeration.sum_length,CandidateEnumeration.prod_length,
    CandidateEnumeration.fin_length,CandidateEnumeration.bool_vertices,List.length_cons,List.length_nil,hlabels]
  rw [show n*2+n*(2*(DyadicEdgeWeights.depth n+2))=2*n*(DyadicEdgeWeights.depth n+3) by ring]
  exact Nat.mul_le_mul_left _ (by omega)

def nodeVectorControlBudget {R : Type*} [Semiring R] (n fee child : R) : R :=
  BinaryFilter.controlBudget (2*n*(n+4)) fee child

theorem nodeVector_control_paid {n fee child : ℕ} (D : Input n) (l : Labels n) (test : RawNode n → (Bool × ℕ) × ℕ)
    (exactTest : ∀ x, (test x).1.1=true ↔ EdgeToVertex.Active D.graph (labelAt l) x)
    (each : ∀ x, (test x).1.2≤fee ∧ (test x).2≤child) :
    (nodeVectorWithControl D l test exactTest).2 ≤ nodeVectorControlBudget n fee child :=
  (BinaryFilter.run_paid test (rawEnumeration n).enumeration.vertices fee child (fun x _ => each x)).trans
    (BinaryFilter.controlBudget_mono (rawEnumeration_length n) le_rfl le_rfl)

def nodeVectorBudget {R : Type*} [Semiring R] (n cap : R) : R := 256*(n+4)^2+2*n*(n+4)*(cap+24)+5

theorem nodeVectorWithCost_paid {n : ℕ} (D : Input n) (l : Labels n) (test : RawNode n → Bool × ℕ)
    (exactTest : ∀ x, (test x).1=true ↔ EdgeToVertex.Active D.graph (labelAt l) x) (cap : ℕ)
    (cost : ∀ x, (test x).2 ≤ cap) : (nodeVectorWithCost D l test exactTest).2 ≤ nodeVectorBudget n cap := by
  have hdepth : DyadicEdgeWeights.depth n ≤ n+1 := Nat.add_le_add_right (Nat.log_le_self 2 n) 1
  have hlabels : (finiteLabels n).enumeration.vertices.length = DyadicEdgeWeights.depth n+2 := by
    simp only [finiteLabels,CandidateEnumeration.pack_vertices,List.length_cons,List.length_map,List.length_finRange]
  have hlabelWork : (finiteLabels n).work=16*(DyadicEdgeWeights.depth n+2)+16 := by
    simp only [finiteLabels,CandidateEnumeration.pack]
  let candidates := rawEnumeration n
  have length : candidates.enumeration.vertices.length ≤ 2*n*(n+4) := rawEnumeration_length n
  have work : candidates.work ≤ 256*(n+4)^2 := by
    simp only [candidates,rawEnumeration,CandidateEnumeration.sum_work,CandidateEnumeration.prod_work,
      CandidateEnumeration.fin_work,CandidateEnumeration.bool_work,CandidateEnumeration.fin_length,
      CandidateEnumeration.prod_length,CandidateEnumeration.bool_vertices,List.length_cons,List.length_nil,hlabels,hlabelWork]
    have scaled := Nat.mul_le_mul_left n hdepth
    nlinarith only [hdepth,scaled]
  have filtered := filterWithCost_paid test candidates.enumeration.vertices cap cost
  have copied : (selectedNodes D l test exactTest).1.length ≤ candidates.enumeration.vertices.length := by
    simp only [selectedNodes,selectedNodesFrom,refineNodes,List.length_map,List.length_attach,filterWithCost_value]
    exact List.length_filter_le _ _
  change candidates.work+(filterWithCost test candidates.enumeration.vertices).2+
    16*(selectedNodes D l test exactTest).1.length+4 ≤ _
  unfold nodeVectorBudget
  have h := filtered.trans (Nat.add_le_add_right (Nat.mul_le_mul_right (cap+8) length) 1)
  have j := Nat.mul_le_mul_left 16 (copied.trans length)
  rw [Nat.mul_add] at h
  rw [Nat.mul_add]
  omega

def buildWithLabels {n : ℕ} (D : Input n) (l : Labels n) : Prepared D :=
  let es := edges D
  let v := nodeVector D l
  assemble D l v (Vector.ofFn fun x => nodeWeight v[x.val].val)
    (Vector.ofFn fun x => FractionalCoverRawCore.sumCodes (es.map (edgeCharge D l v[x.val].val)))

def build {n : ℕ} (D : Input n) : Prepared D := buildWithLabels D (labelTable D)

def indexEquiv {n : ℕ} (D : Input n) : Fin (build D).size ≃ Node D (labelTable D) :=
  List.Nodup.getEquivOfForallMemList _ (nodes_nodup D (labelTable D)) (nodes_mem D (labelTable D))

@[simp] theorem indexEquiv_apply {n : ℕ} (D : Input n) (i : Fin (build D).size) :
    indexEquiv D i = (build D).vertices[i.val] := rfl

theorem build_adj {n : ℕ} (D : Input n) (i j : Fin (build D).size) :
    (build D).data.graph.Adj i j ↔
      (EdgeToVertex.graph D.graph (labelAt (labelTable D))).Adj (indexEquiv D i) (indexEquiv D j) := by
  have h : (build D).data.graph.Adj i j ↔ adjacent D (labelTable D)
      (build D).vertices[i.val].val (build D).vertices[j.val].val = true := by
    simp only [EncodedUnitCostReplication.Input.graph, build, buildWithLabels, assemble, Vector.getElem_ofFn]
  rw [← indexEquiv_apply D i, ← indexEquiv_apply D j] at h
  exact h.trans (adjacent_iff D (labelTable D) (indexEquiv D i).val (indexEquiv D j).val)

theorem build_weight {n : ℕ} (D : Input n) (i : Fin (build D).size) :
    (build D).data.weight i = EdgeToVertex.weight D.graph (labelAt (labelTable D))
      (DyadicEdgeWeights.value n) (indexEquiv D i) := by
  have h : EdgeToVertex.Active D.graph (labelAt (labelTable D)) (indexEquiv D i).val :=
    (indexEquiv D i).property
  unfold EdgeToVertex.weight
  rw [EdgeToVertex.rawWeight.eq_def, ite_eq_left h]
  simp only [EncodedUnitCostReplication.Input.weight, build, buildWithLabels, assemble, Vector.getElem_ofFn]
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
  simp only [EncodedUnitCostReplication.Input.cost, build, buildWithLabels, assemble, Vector.getElem_ofFn]
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
