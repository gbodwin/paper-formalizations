import DirectedFlowCutGap.PathExtraction

/-!
# Actual directed edge weights, walks, distances, and cuts

The edge model of Section 2.1 and Theorems 30–31 of arXiv:2604.03412v3.
Edges are ordered pairs satisfying `Digraph.Adj`, exactly as in the source;
there are no parallel-edge identities or symmetry assumptions. Finite
nonnegative costs and weights may vanish. Every consecutive edge contributes
to path length, including the first and last. Walk length counts repetitions.

Loop erasure is proved to preserve edge support by first restricting the graph
to the walk's actual edges. This is stronger than vertex-support containment.
Length-zero self paths have zero cost and cannot be cut. Graph self-loops are
allowed and included in total edge sums, though no simple path uses a loop.
The reductions themselves are not assumed or proved in this module.
-/

namespace DirectedFlowCutGap

noncomputable section

open scoped BigOperators NNReal ENNReal

attribute [local instance] Classical.propDecidable

variable {V : Type*} [DecidableEq V]

/-- Restrict adjacency to a specified set of ordered pairs. -/
def restrictEdges (G : Digraph V) (E : Finset (V × V)) : Digraph V where
  Adj s t := G.Adj s t ∧ (s, t) ∈ E

namespace SimplePath

variable {G H : Digraph V} {s u t : V}

/-- The actual edge at an index of a simple directed path. -/
def edgeAt (p : SimplePath G s t) (i : Fin p.edgeLength) : V × V :=
  (p.vertex i.castSucc, p.vertex i.succ)

/-- All consecutive directed edges, including those incident to endpoints. -/
def edges (p : SimplePath G s t) : Finset (V × V) :=
  Finset.univ.image p.edgeAt

@[simp] theorem mem_edges (p : SimplePath G s t) (e : V × V) :
    e ∈ p.edges ↔ ∃ i, p.edgeAt i = e := by simp [edges]

theorem edgeAt_mem_edges (p : SimplePath G s t) (i : Fin p.edgeLength) :
    p.edgeAt i ∈ p.edges := (p.mem_edges _).mpr ⟨i, rfl⟩

omit [DecidableEq V] in
theorem edgeAt_injective (p : SimplePath G s t) : Function.Injective p.edgeAt := by
  intro i j h
  have h' := p.injective (congrArg Prod.fst h)
  exact Fin.ext (congrArg (fun k : Fin (p.edgeLength + 1) => k.val) h')

@[simp] theorem card_edges (p : SimplePath G s t) : p.edges.card = p.edgeLength := by
  rw [edges, Finset.card_image_of_injective _ p.edgeAt_injective]
  simp

theorem edge_adj (p : SimplePath G s t) {e : V × V} (h : e ∈ p.edges) :
    G.Adj e.1 e.2 := by
  obtain ⟨i, rfl⟩ := (p.mem_edges e).mp h
  exact p.adjacent i

theorem edge_ne (p : SimplePath G s t) {e : V × V} (h : e ∈ p.edges) :
    e.1 ≠ e.2 := by
  obtain ⟨i, rfl⟩ := (p.mem_edges e).mp h
  intro he
  have hi := congrArg Fin.val (p.injective he)
  simp at hi

@[simp] theorem refl_edges (G : Digraph V) (s : V) : (refl G s).edges = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro e he
  obtain ⟨i, _hi⟩ := (mem_edges _ e).mp he
  exact Fin.elim0 i

@[simp] theorem edge_edges (h : G.Adj s t) (hne : s ≠ t) :
    (edge h hne).edges = {(s, t)} := by
  ext e
  simp only [mem_edges, Finset.mem_singleton]
  constructor
  · rintro ⟨i, hi⟩
    change Fin 1 at i
    have hi0 : i = 0 := Subsingleton.elim _ _
    subst i
    exact hi.symm
  · intro he
    exact ⟨(0 : Fin 1), he.symm⟩

omit [DecidableEq V] in
/-- Injectivity forces a self path to have no edges, even when G has loops. -/
theorem edgeLength_eq_zero_of_self (p : SimplePath G s s) : p.edgeLength = 0 := by
  have h := congrArg Fin.val (p.injective (p.source_eq.trans p.target_eq.symm))
  change 0 = p.edgeLength at h
  exact h.symm

@[simp] theorem self_edges (p : SimplePath G s s) : p.edges = ∅ := by
  apply Finset.card_eq_zero.mp
  rw [p.card_edges, p.edgeLength_eq_zero_of_self]

/-- Sum every edge of the path; no endpoint exclusion applies to edge length. -/
def edgeWeight (p : SimplePath G s t) (w : V × V → ℝ≥0) : ℝ≥0 :=
  ∑ e ∈ p.edges, w e

theorem edgeWeight_eq_sum (p : SimplePath G s t) (w : V × V → ℝ≥0) :
    p.edgeWeight w = ∑ i : Fin p.edgeLength, w (p.edgeAt i) := by
  exact Finset.sum_image (fun i _ j _ h => p.edgeAt_injective h)

@[simp] theorem refl_edgeWeight (G : Digraph V) (s : V) (w : V × V → ℝ≥0) :
    (refl G s).edgeWeight w = 0 := by simp [edgeWeight]

@[simp] theorem edge_edgeWeight (h : G.Adj s t) (hne : s ≠ t)
    (w : V × V → ℝ≥0) : (edge h hne).edgeWeight w = w (s, t) := by
  simp [edgeWeight]

@[simp] theorem edgeWeight_zero (p : SimplePath G s t) :
    p.edgeWeight (fun _ => 0) = 0 := by simp [edgeWeight]

@[simp] theorem edgeWeight_unit (p : SimplePath G s t) :
    p.edgeWeight (fun _ => 1) = (p.edgeLength : ℝ≥0) := by simp [edgeWeight]

theorem edgeWeight_mono (p : SimplePath G s t) {w w' : V × V → ℝ≥0}
    (h : ∀ e ∈ p.edges, w e ≤ w' e) : p.edgeWeight w ≤ p.edgeWeight w' :=
  Finset.sum_le_sum h

/-- Change only the graph; retain the complete vertex sequence. -/
def changeGraph (p : SimplePath G s t)
    (h : ∀ i : Fin p.edgeLength, H.Adj (p.vertex i.castSucc) (p.vertex i.succ)) :
    SimplePath H s t where
  edgeLength := p.edgeLength
  vertex := p.vertex
  source_eq := p.source_eq
  target_eq := p.target_eq
  injective := p.injective
  adjacent := h

@[simp] theorem changeGraph_edges (p : SimplePath G s t)
    (h : ∀ i : Fin p.edgeLength, H.Adj (p.vertex i.castSucc) (p.vertex i.succ)) :
    (p.changeGraph h).edges = p.edges := rfl

/-- Interpret a path in any edge restriction that contains all its edges. -/
def restrictTo (p : SimplePath G s t) (E : Finset (V × V)) (h : p.edges ⊆ E) :
    SimplePath (restrictEdges G E) s t :=
  p.changeGraph fun i => ⟨p.adjacent i, h (p.edgeAt_mem_edges i)⟩

/-- Forget an edge restriction without changing any path edge. -/
def forgetRestriction {E : Finset (V × V)} (p : SimplePath (restrictEdges G E) s t) :
    SimplePath G s t := p.changeGraph fun i => (p.adjacent i).1

theorem forgetRestriction_edges_subset {E : Finset (V × V)}
    (p : SimplePath (restrictEdges G E) s t) : p.forgetRestriction.edges ⊆ E := by
  intro e he
  exact (p.edge_adj he).2

end SimplePath

namespace DirectedWalk

variable {G H : Digraph V} {s u t : V}

/-- Actual directed edges traversed, with repetitions forgotten only in the support. -/
def edges : {s t : V} → DirectedWalk G s t → Finset (V × V)
  | _, _, .refl _ => ∅
  | s, _, .cons (u := u) _ q => insert (s, u) q.edges

/-- Conventional additive walk length counts every traversal, including loops. -/
def edgeWeight (w : V × V → ℝ≥0) : {s t : V} → DirectedWalk G s t → ℝ≥0
  | _, _, .refl _ => 0
  | s, _, .cons (u := u) _ q => w (s, u) + q.edgeWeight w

theorem edge_adj (q : DirectedWalk G s t) {e : V × V} (h : e ∈ q.edges) :
    G.Adj e.1 e.2 := by
  induction q with
  | refl => simp [edges] at h
  | @cons s u t ha q ih =>
    rcases Finset.mem_insert.mp h with rfl | he
    · exact ha
    · exact ih he

/-- An adjacency-preserving identity map changes no edge of a walk. -/
def changeGraph (h : ∀ a b, G.Adj a b → H.Adj a b) :
    {s t : V} → DirectedWalk G s t → DirectedWalk H s t
  | _, _, .refl s => .refl s
  | _, _, .cons he q => .cons (h _ _ he) (q.changeGraph h)

/-- Lift a walk into a restriction containing its support. -/
def restrictTo : {s t : V} → (q : DirectedWalk G s t) →
    (E : Finset (V × V)) → q.edges ⊆ E → DirectedWalk (restrictEdges G E) s t
  | _, _, .refl s, _, _ => .refl s
  | _, _, .cons he q, E, h =>
      .cons ⟨he, h (Finset.mem_insert_self _ _)⟩
        (q.restrictTo E (fun _ hm => h (Finset.mem_insert_of_mem hm)))

theorem append_edges (p : DirectedWalk G s u) (q : DirectedWalk G u t) :
    (p.append q).edges = p.edges ∪ q.edges := by
  induction p with
  | refl => simp [append, edges]
  | cons h p ih => simp [append, edges, ih, Finset.insert_union]

omit [DecidableEq V] in
theorem append_edgeWeight (p : DirectedWalk G s u) (q : DirectedWalk G u t)
    (w : V × V → ℝ≥0) : (p.append q).edgeWeight w = p.edgeWeight w + q.edgeWeight w := by
  induction p with
  | refl => simp [append, edgeWeight]
  | cons h p ih => simp [append, edgeWeight, ih, add_assoc]

/-- The weight of edge support is at most the length with multiplicity. -/
theorem sum_edges_le_edgeWeight (q : DirectedWalk G s t) (w : V × V → ℝ≥0) :
    (∑ e ∈ q.edges, w e) ≤ q.edgeWeight w := by
  induction q with
  | refl => simp [edges, edgeWeight]
  | @cons s u t h q ih =>
    change (∑ e ∈ insert (s, u) q.edges, w e) ≤ w (s, u) + q.edgeWeight w
    by_cases hm : (s, u) ∈ q.edges
    · rw [Finset.insert_eq_of_mem hm]
      exact ih.trans (le_add_of_nonneg_left bot_le)
    · rw [Finset.sum_insert hm]
      exact add_le_add (le_refl _) ih

/-- Genuine loop erasure: every remaining edge was traversed by the walk. -/
theorem exists_simplePath_edges_subset (q : DirectedWalk G s t) :
    ∃ p : SimplePath G s t, p.edges ⊆ q.edges := by
  obtain ⟨p, _hp⟩ := (q.restrictTo q.edges (fun _ he => he)).exists_simplePath
  exact ⟨p.forgetRestriction, p.forgetRestriction_edges_subset⟩

/-- Nonnegative edge lengths never increase under edge-preserving loop erasure. -/
theorem exists_simplePath_edgeWeight_le (q : DirectedWalk G s t)
    (w : V × V → ℝ≥0) :
    ∃ p : SimplePath G s t, p.edges ⊆ q.edges ∧ p.edgeWeight w ≤ q.edgeWeight w := by
  obtain ⟨p, hp⟩ := q.exists_simplePath_edges_subset
  exact ⟨p, hp, (Finset.sum_le_sum_of_subset hp).trans (q.sum_edges_le_edgeWeight w)⟩

omit [DecidableEq V] in
/-- A sequence produces a walk of exactly the sum of its consecutive edge lengths. -/
theorem exists_of_sequence_edgeWeight {n : ℕ} (v : Fin (n + 1) → V)
    (h : ∀ i : Fin n, G.Adj (v i.castSucc) (v i.succ)) (w : V × V → ℝ≥0) :
    ∃ q : DirectedWalk G (v 0) (v (Fin.last n)),
      q.edgeWeight w = ∑ i : Fin n, w (v i.castSucc, v i.succ) := by
  induction n with
  | zero => exact ⟨.refl (v 0), by simp [edgeWeight]⟩
  | succ n ih =>
    obtain ⟨q, hq⟩ := ih (fun i => v i.succ) (fun i => h i.succ)
    refine ⟨.cons (h 0) q, ?_⟩
    change w (v 0, v (Fin.succ 0)) + q.edgeWeight w = _
    rw [hq, Fin.sum_univ_succ]
    rfl

end DirectedWalk

namespace SimplePath

variable {G : Digraph V} {s u t : V}

/-- Every simple path has a concrete walk of the same edge length. -/
theorem exists_directedWalk_edgeWeight (p : SimplePath G s t) (w : V × V → ℝ≥0) :
    ∃ q : DirectedWalk G s t, q.edgeWeight w = p.edgeWeight w := by
  cases p with
  | mk n v hs ht hi ha =>
    subst s
    subst t
    obtain ⟨q, hq⟩ := DirectedWalk.exists_of_sequence_edgeWeight v ha w
    refine ⟨q, ?_⟩
    rw [edgeWeight_eq_sum]
    exact hq

/-- Composition followed by erasure retains only actual edges of the two paths. -/
theorem exists_composition_edges_subset (p : SimplePath G s u) (q : SimplePath G u t) :
    ∃ r : SimplePath G s t, r.edges ⊆ p.edges ∪ q.edges := by
  let E := p.edges ∪ q.edges
  let a := p.restrictTo E Finset.subset_union_left
  let b := q.restrictTo E Finset.subset_union_right
  obtain ⟨r, _hr⟩ := a.exists_composition b
  exact ⟨r.forgetRestriction, r.forgetRestriction_edges_subset⟩

/-- Ordinary edge triangle composition has no extra middle-vertex charge. -/
theorem exists_composition_edgeWeight_le (p : SimplePath G s u) (q : SimplePath G u t)
    (w : V × V → ℝ≥0) : ∃ r : SimplePath G s t,
      r.edges ⊆ p.edges ∪ q.edges ∧ r.edgeWeight w ≤ p.edgeWeight w + q.edgeWeight w := by
  obtain ⟨r, hr⟩ := p.exists_composition_edges_subset q
  refine ⟨r, hr, (Finset.sum_le_sum_of_subset hr).trans ?_⟩
  calc
    (∑ e ∈ p.edges ∪ q.edges, w e) ≤
        (∑ e ∈ p.edges ∪ q.edges, w e) + ∑ e ∈ p.edges ∩ q.edges, w e :=
      le_add_of_nonneg_right bot_le
    _ = _ := Finset.sum_union_inter

end SimplePath

/-- Extended edge distance is the infimum over actual simple directed paths. -/
def edgeDistance (G : Digraph V) (w : V × V → ℝ≥0) (s t : V) : ℝ≥0∞ :=
  ⨅ p : SimplePath G s t, (p.edgeWeight w : ℝ≥0∞)

theorem le_edgeDistance_iff (G : Digraph V) (w : V × V → ℝ≥0) (s t : V)
    (r : ℝ≥0∞) :
    r ≤ edgeDistance G w s t ↔ ∀ p : SimplePath G s t, r ≤ (p.edgeWeight w : ℝ≥0∞) :=
  le_iInf_iff

theorem coe_le_edgeDistance_iff (G : Digraph V) (w : V × V → ℝ≥0) (s t : V)
    (r : ℝ≥0) :
    (r : ℝ≥0∞) ≤ edgeDistance G w s t ↔ ∀ p : SimplePath G s t, r ≤ p.edgeWeight w := by
  simp only [le_edgeDistance_iff, ENNReal.coe_le_coe]

theorem edgeDistance_le_weight {G : Digraph V} (w : V × V → ℝ≥0) {s t : V}
    (p : SimplePath G s t) : edgeDistance G w s t ≤ (p.edgeWeight w : ℝ≥0∞) :=
  iInf_le _ p

theorem edgeDistance_le_walk_weight {G : Digraph V} (w : V × V → ℝ≥0) {s t : V}
    (q : DirectedWalk G s t) : edgeDistance G w s t ≤ (q.edgeWeight w : ℝ≥0∞) := by
  obtain ⟨p, _hp, hw⟩ := q.exists_simplePath_edgeWeight_le w
  exact (edgeDistance_le_weight w p).trans (ENNReal.coe_le_coe.mpr hw)

theorem le_edgeDistance_iff_all_walks (G : Digraph V) (w : V × V → ℝ≥0) (s t : V)
    (r : ℝ≥0∞) : r ≤ edgeDistance G w s t ↔
      ∀ q : DirectedWalk G s t, r ≤ (q.edgeWeight w : ℝ≥0∞) := by
  constructor
  · intro h q
    exact h.trans (edgeDistance_le_walk_weight w q)
  · intro h
    rw [le_edgeDistance_iff]
    intro p
    obtain ⟨q, hq⟩ := p.exists_directedWalk_edgeWeight w
    simpa [hq] using h q

/-- Infimizing over walks with traversal multiplicity gives the same distance. -/
theorem edgeDistance_eq_iInf_walkWeight (G : Digraph V) (w : V × V → ℝ≥0) (s t : V) :
    edgeDistance G w s t = ⨅ q : DirectedWalk G s t, (q.edgeWeight w : ℝ≥0∞) := by
  apply le_antisymm
  · exact le_iInf fun q => edgeDistance_le_walk_weight w q
  · rw [le_edgeDistance_iff]
    intro p
    obtain ⟨q, hq⟩ := p.exists_directedWalk_edgeWeight w
    simpa only [hq] using
      (iInf_le (fun q : DirectedWalk G s t => (q.edgeWeight w : ℝ≥0∞)) q)

theorem edgeDistance_eq_top_iff (G : Digraph V) (w : V × V → ℝ≥0) (s t : V) :
    edgeDistance G w s t = ⊤ ↔ ¬Nonempty (SimplePath G s t) := by
  constructor
  · intro h ⟨p⟩
    have hp := edgeDistance_le_weight w p
    rw [h] at hp
    exact ENNReal.coe_ne_top (top_le_iff.mp hp)
  · intro h
    apply top_unique
    rw [le_edgeDistance_iff]
    intro p
    exact (h ⟨p⟩).elim

theorem edgeDistance_eq_top_iff_no_walk (G : Digraph V) (w : V × V → ℝ≥0) (s t : V) :
    edgeDistance G w s t = ⊤ ↔ ¬Nonempty (DirectedWalk G s t) := by
  rw [edgeDistance_eq_top_iff, nonempty_simplePath_iff_directedWalk]

@[simp] theorem edgeDistance_self (G : Digraph V) (w : V × V → ℝ≥0) (s : V) :
    edgeDistance G w s s = 0 := by
  apply le_antisymm _ bot_le
  simpa using edgeDistance_le_weight w (SimplePath.refl G s)

theorem edgeDistance_le_of_adj {G : Digraph V} (w : V × V → ℝ≥0) {s t : V}
    (h : G.Adj s t) : edgeDistance G w s t ≤ (w (s, t) : ℝ≥0∞) := by
  by_cases hst : s = t
  · subst t
    simp
  · simpa using edgeDistance_le_weight w (SimplePath.edge h hst)

theorem edgeDistance_mono (G : Digraph V) {w w' : V × V → ℝ≥0} (s t : V)
    (h : ∀ a b, G.Adj a b → w (a, b) ≤ w' (a, b)) :
    edgeDistance G w s t ≤ edgeDistance G w' s t := by
  exact iInf_mono fun p => ENNReal.coe_le_coe.mpr
    (p.edgeWeight_mono fun e he => h e.1 e.2 (p.edge_adj he))

/-- Values assigned to nonedges do not affect the distance. -/
theorem edgeDistance_congr_on_edges (G : Digraph V) {w w' : V × V → ℝ≥0} (s t : V)
    (h : ∀ a b, G.Adj a b → w (a, b) = w' (a, b)) :
    edgeDistance G w s t = edgeDistance G w' s t := by
  apply le_antisymm
  · exact edgeDistance_mono G s t (fun a b ha => le_of_eq (h a b ha))
  · exact edgeDistance_mono G s t (fun a b ha => le_of_eq (h a b ha).symm)

theorem edgeDistance_attained [Fintype V] {G : Digraph V} (w : V × V → ℝ≥0)
    {s t : V} (h : Nonempty (SimplePath G s t)) :
    ∃ p : SimplePath G s t, edgeDistance G w s t = (p.edgeWeight w : ℝ≥0∞) := by
  obtain ⟨p, _hp, hmin⟩ := Set.exists_min_image
    (Set.univ : Set (SimplePath G s t)) (fun p => p.edgeWeight w)
    (Set.toFinite _) (by rcases h with ⟨p⟩; exact ⟨p, Set.mem_univ p⟩)
  refine ⟨p, le_antisymm (edgeDistance_le_weight w p) ?_⟩
  exact (coe_le_edgeDistance_iff G w s t (p.edgeWeight w)).mpr
    (fun q => hmin q (Set.mem_univ q))

theorem edgeDistance_triangle [Fintype V] (G : Digraph V) (w : V × V → ℝ≥0)
    (s u t : V) : edgeDistance G w s t ≤ edgeDistance G w s u + edgeDistance G w u t := by
  by_cases hs : Nonempty (SimplePath G s u)
  · by_cases ht : Nonempty (SimplePath G u t)
    · obtain ⟨p, hp⟩ := edgeDistance_attained w hs
      obtain ⟨q, hq⟩ := edgeDistance_attained w ht
      obtain ⟨r, _hr, hw⟩ := p.exists_composition_edgeWeight_le q w
      calc
        edgeDistance G w s t ≤ (r.edgeWeight w : ℝ≥0∞) := edgeDistance_le_weight w r
        _ ≤ ((p.edgeWeight w + q.edgeWeight w : ℝ≥0) : ℝ≥0∞) :=
          ENNReal.coe_le_coe.mpr hw
        _ = _ := by rw [hp, hq]; simp
    · rw [(edgeDistance_eq_top_iff G w u t).mpr ht]
      simp
  · rw [(edgeDistance_eq_top_iff G w s u).mpr hs]
    simp

/-- An edge cut meets every demanded path in an actual directed edge. -/
def EdgeCutsPair (G : Digraph V) (X : Finset (V × V)) (s t : V) : Prop :=
  ∀ p : SimplePath G s t, ∃ e ∈ p.edges, e ∈ X

/-- Avoid every selected edge, including edges incident to demand endpoints. -/
def SimplePath.EdgeAvoids {G : Digraph V} {s t : V} (p : SimplePath G s t)
    (X : Finset (V × V)) : Prop := ∀ e ∈ p.edges, e ∉ X

theorem not_edgeCutsPair_iff (G : Digraph V) (X : Finset (V × V)) (s t : V) :
    ¬EdgeCutsPair G X s t ↔ ∃ p : SimplePath G s t, p.EdgeAvoids X := by
  simp only [EdgeCutsPair, SimplePath.EdgeAvoids, not_forall, not_exists, not_and]

theorem not_edgeCutsPair_self (G : Digraph V) (X : Finset (V × V)) (s : V) :
    ¬EdgeCutsPair G X s s := by
  intro h
  simpa using h (SimplePath.refl G s)

theorem edgeCutsPair_mono {G : Digraph V} {X Y : Finset (V × V)} {s t : V}
    (hXY : X ⊆ Y) (h : EdgeCutsPair G X s t) : EdgeCutsPair G Y s t := by
  intro p
  obtain ⟨e, he, hx⟩ := h p
  exact ⟨e, he, hXY hx⟩

/-- Edge deletion retains every vertex, including both endpoints. -/
def edgeDeletedGraph (G : Digraph V) (X : Finset (V × V)) : Digraph V where
  Adj s t := G.Adj s t ∧ (s, t) ∉ X

namespace SimplePath

variable {G : Digraph V} {s t : V}

def liftEdgeAvoiding (p : SimplePath G s t) (X : Finset (V × V)) (h : p.EdgeAvoids X) :
    SimplePath (edgeDeletedGraph G X) s t :=
  p.changeGraph fun i => ⟨p.adjacent i, h _ (p.edgeAt_mem_edges i)⟩

def forgetEdgeDeletion {X : Finset (V × V)} (p : SimplePath (edgeDeletedGraph G X) s t) :
    SimplePath G s t := p.changeGraph fun i => (p.adjacent i).1

theorem forgetEdgeDeletion_avoids {X : Finset (V × V)}
    (p : SimplePath (edgeDeletedGraph G X) s t) : p.forgetEdgeDeletion.EdgeAvoids X := by
  intro e he
  exact (p.edge_adj he).2

end SimplePath

theorem edgeDeletedGraph_path_iff (G : Digraph V) (X : Finset (V × V)) (s t : V) :
    Nonempty (SimplePath (edgeDeletedGraph G X) s t) ↔
      ∃ p : SimplePath G s t, p.EdgeAvoids X := by
  constructor
  · rintro ⟨p⟩
    exact ⟨p.forgetEdgeDeletion, p.forgetEdgeDeletion_avoids⟩
  · rintro ⟨p, hp⟩
    exact ⟨p.liftEdgeAvoiding X hp⟩

theorem edgeCutsPair_iff_edgeDeletedGraph (G : Digraph V) (X : Finset (V × V)) (s t : V) :
    EdgeCutsPair G X s t ↔ ¬Nonempty (SimplePath (edgeDeletedGraph G X) s t) := by
  rw [edgeDeletedGraph_path_iff, ← not_edgeCutsPair_iff, not_not]

theorem edgeCutsPair_iff_no_deleted_walk (G : Digraph V) (X : Finset (V × V)) (s t : V) :
    EdgeCutsPair G X s t ↔ ¬Nonempty (DirectedWalk (edgeDeletedGraph G X) s t) := by
  rw [edgeCutsPair_iff_edgeDeletedGraph, nonempty_simplePath_iff_directedWalk]

/-- Feasibility for an explicit (possibly empty) family of demand pairs. -/
def IsFractionalEdgeCut (G : Digraph V) (w : V × V → ℝ≥0) (D : Set (V × V)) : Prop :=
  ∀ s t, (s, t) ∈ D → 1 ≤ edgeDistance G w s t

def IsIntegralEdgeCut (G : Digraph V) (X : Finset (V × V)) (D : Set (V × V)) : Prop :=
  ∀ s t, (s, t) ∈ D → EdgeCutsPair G X s t

def edgeThresholdDemands (G : Digraph V) (w : V × V → ℝ≥0) : Set (V × V) :=
  {st | 1 ≤ edgeDistance G w st.1 st.2}

theorem isFractionalEdgeCut_iff (G : Digraph V) (w : V × V → ℝ≥0) (D : Set (V × V)) :
    IsFractionalEdgeCut G w D ↔
      ∀ s t, (s, t) ∈ D → ∀ p : SimplePath G s t, 1 ≤ p.edgeWeight w := by
  simp only [IsFractionalEdgeCut, ← ENNReal.coe_one, coe_le_edgeDistance_iff]

theorem isFractionalEdgeCut_iff_all_walks (G : Digraph V) (w : V × V → ℝ≥0)
    (D : Set (V × V)) : IsFractionalEdgeCut G w D ↔
      ∀ s t, (s, t) ∈ D → ∀ q : DirectedWalk G s t, 1 ≤ q.edgeWeight w := by
  simp only [IsFractionalEdgeCut, ← ENNReal.coe_one,
    le_edgeDistance_iff_all_walks, ENNReal.coe_le_coe]

theorem isFractionalEdgeCut_thresholdDemands (G : Digraph V) (w : V × V → ℝ≥0) :
    IsFractionalEdgeCut G w (edgeThresholdDemands G w) := by
  intro s t h
  exact h

/-- Integral indicator weights coincide with hitting all path edges. -/
def edgeCutIndicator (X : Finset (V × V)) (e : V × V) : ℝ≥0 := if e ∈ X then 1 else 0

theorem edgeCutsPair_iff_indicator (G : Digraph V) (X : Finset (V × V)) (s t : V) :
    EdgeCutsPair G X s t ↔ 1 ≤ edgeDistance G (edgeCutIndicator X) s t := by
  rw [← ENNReal.coe_one, coe_le_edgeDistance_iff]
  constructor
  · intro h p
    obtain ⟨e, he, hx⟩ := h p
    calc
      1 = edgeCutIndicator X e := by simp [edgeCutIndicator, hx]
      _ ≤ p.edgeWeight (edgeCutIndicator X) := Finset.single_le_sum (fun _ _ => bot_le) he
  · intro h p
    by_contra hn
    have hz : p.edgeWeight (edgeCutIndicator X) = 0 := by
      apply Finset.sum_eq_zero
      intro e he
      have hx : e ∉ X := fun hx => hn ⟨e, he, hx⟩
      simp [edgeCutIndicator, hx]
    have hp := h p
    rw [hz] at hp
    exact (not_le_of_gt zero_lt_one) hp

theorem isIntegralEdgeCut_iff_indicator (G : Digraph V) (X : Finset (V × V))
    (D : Set (V × V)) :
    IsIntegralEdgeCut G X D ↔ IsFractionalEdgeCut G (edgeCutIndicator X) D := by
  simp only [IsIntegralEdgeCut, IsFractionalEdgeCut, edgeCutsPair_iff_indicator]

/-- The actual finite edge set. Nonedges never contribute to any objective. -/
def graphEdges [Fintype V] (G : Digraph V) : Finset (V × V) :=
  Finset.univ.filter (fun e => G.Adj e.1 e.2)

omit [DecidableEq V] in
@[simp] theorem mem_graphEdges [Fintype V] (G : Digraph V) (e : V × V) :
    e ∈ graphEdges G ↔ G.Adj e.1 e.2 := by simp [graphEdges]

/-- Cut cost ignores selected nonedges; every cut can be normalized to actual edges. -/
def edgeCutCost (G : Digraph V) (cost : V × V → ℝ≥0) (X : Finset (V × V)) : ℝ≥0 :=
  ∑ e ∈ X.filter (fun e => G.Adj e.1 e.2), cost e

/-- Total fractional edge weight, including any graph self-loops. -/
def totalEdgeWeight [Fintype V] (G : Digraph V) (w : V × V → ℝ≥0) : ℝ≥0 :=
  ∑ e ∈ graphEdges G, w e

/-- Fractional objective over actual edges, with finite nonnegative costs. -/
def weightedEdgeCost [Fintype V] (G : Digraph V) (cost w : V × V → ℝ≥0) : ℝ≥0 :=
  ∑ e ∈ graphEdges G, cost e * w e

theorem SimplePath.edges_subset_graphEdges [Fintype V] {G : Digraph V} {s t : V}
    (p : SimplePath G s t) : p.edges ⊆ graphEdges G := by
  intro e he
  exact (mem_graphEdges G e).mpr (p.edge_adj he)

theorem SimplePath.edgeWeight_le_total [Fintype V] {G : Digraph V} {s t : V}
    (p : SimplePath G s t) (w : V × V → ℝ≥0) : p.edgeWeight w ≤ totalEdgeWeight G w :=
  Finset.sum_le_sum_of_subset p.edges_subset_graphEdges

theorem edgeCutsPair_filter_actual (G : Digraph V) (X : Finset (V × V)) (s t : V) :
    EdgeCutsPair G (X.filter fun e => G.Adj e.1 e.2) s t ↔ EdgeCutsPair G X s t := by
  constructor
  · exact edgeCutsPair_mono (Finset.filter_subset _ _)
  · intro h p
    obtain ⟨e, he, hx⟩ := h p
    exact ⟨e, he, Finset.mem_filter.mpr ⟨hx, p.edge_adj he⟩⟩

omit [DecidableEq V] in
@[simp] theorem edgeCutCost_filter_actual (G : Digraph V) (cost : V × V → ℝ≥0)
    (X : Finset (V × V)) :
    edgeCutCost G cost (X.filter fun e => G.Adj e.1 e.2) = edgeCutCost G cost X := by
  simp [edgeCutCost, Finset.filter_filter]

omit [DecidableEq V] in
@[simp] theorem edgeCutCost_unit (G : Digraph V) (X : Finset (V × V)) :
    edgeCutCost G (fun _ => 1) X =
      ((X.filter fun e => G.Adj e.1 e.2).card : ℝ≥0) := by
  simp [edgeCutCost]

/-- The integral objective is exactly the fractional objective of its indicator. -/
theorem weightedEdgeCost_indicator [Fintype V] (G : Digraph V)
    (cost : V × V → ℝ≥0) (X : Finset (V × V)) :
    weightedEdgeCost G cost (edgeCutIndicator X) = edgeCutCost G cost X := by
  unfold weightedEdgeCost edgeCutCost
  simp only [edgeCutIndicator, mul_ite, mul_one, mul_zero, ← Finset.sum_filter]
  apply Finset.sum_congr
  · ext e
    simp [and_comm]
  · intro e _he
    rfl

omit [DecidableEq V] in
@[simp] theorem weightedEdgeCost_unit [Fintype V] (G : Digraph V) (w : V × V → ℝ≥0) :
    weightedEdgeCost G (fun _ => 1) w = totalEdgeWeight G w := by
  simp [weightedEdgeCost, totalEdgeWeight]

end

end DirectedFlowCutGap
