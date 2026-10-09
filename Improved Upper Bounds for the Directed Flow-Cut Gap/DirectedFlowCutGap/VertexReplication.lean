import DirectedFlowCutGap.ShortcutContraction

/-!
# Vertex replication with complete fibers

This is the static replication step in the repaired Theorem 29 of
Bodwin–Samborska, arXiv:2604.03412v3. A vertex has an explicitly positive
number of clones, every original edge becomes a complete bipartite set of
edges, weights are copied, and costs are one.

Projection of a clone path is a walk, not in general a simple path. Proved
loop erasure gives an original simple path of no larger weight. An arbitrary
clone cut pulls back only through its fully deleted fibers. To respect the
endpoint-excluding convention, demand endpoints use fixed representatives,
while the internal vertices of an avoiding lift may use other surviving
representatives. No assertion identifies a partial fiber with a deleted
original vertex. Normalization, ceiling bounds, and the final asymptotic
flow-cut statement are separate from this graph/count/cost foundation.
-/

namespace DirectedFlowCutGap

noncomputable section

open scoped BigOperators NNReal ENNReal

namespace VertexReplication

variable {V : Type*}

/-- The actual finite family of clones of each original vertex. -/
abbrev Vertex (copies : V → ℕ) := Σ v : V, Fin (copies v)

/-- Replicate every directed edge between all pairs of its endpoint clones. -/
def graph (G : Digraph V) (copies : V → ℕ) : Digraph (Vertex copies) where
  Adj a b := G.Adj a.1 b.1

/-- Every clone keeps its original vertex's weight. -/
def weight (copies : V → ℕ) (w : V → ℝ≥0) (a : Vertex copies) : ℝ≥0 := w a.1

/-- Costs in the replicated instance are genuinely unit costs. -/
def cost (copies : V → ℕ) : Vertex copies → ℝ≥0 := fun _ => 1

/-- One selected clone per vertex; all later demand endpoints use this section. -/
def representative {copies : V → ℕ} (index : ∀ v, Fin (copies v))
    (v : V) : Vertex copies := ⟨v, index v⟩

@[simp] theorem representative_fst {copies : V → ℕ}
    (index : ∀ v, Fin (copies v)) (v : V) : (representative index v).1 = v := rfl

theorem representative_injective {copies : V → ℕ}
    (index : ∀ v, Fin (copies v)) : Function.Injective (representative index) := by
  intro u v h
  exact congrArg Sigma.fst h

/-- Positive replication counts provide canonical first copies. -/
def firstIndex (copies : V → ℕ) (hpos : ∀ v, 1 ≤ copies v) (v : V) :
    Fin (copies v) := ⟨0, hpos v⟩

/-- Lifting an original simple path through any one-clone-per-vertex section
preserves simplicity and every adjacency. -/
def liftPath {G : Digraph V} {copies : V → ℕ} {s t : V}
    (p : SimplePath G s t) (index : ∀ v, Fin (copies v)) :
    SimplePath (graph G copies) (representative index s) (representative index t) where
  edgeLength := p.edgeLength
  vertex i := representative index (p.vertex i)
  source_eq := congrArg (representative index) p.source_eq
  target_eq := congrArg (representative index) p.target_eq
  injective := (representative_injective index).comp p.injective
  adjacent := p.adjacent

variable [DecidableEq V]

/-- Lifting preserves the internal support exactly. -/
theorem liftPath_internalVertices {G : Digraph V} {copies : V → ℕ} {s t : V}
    (p : SimplePath G s t) (index : ∀ v, Fin (copies v)) :
    (liftPath p index).internalVertices = p.internalVertices.image (representative index) := by
  ext a
  constructor
  · intro ha
    obtain ⟨⟨i, hi⟩, hs, ht⟩ := (SimplePath.mem_internalVertices _ a).mp ha
    refine Finset.mem_image.mpr ⟨p.vertex i, (p.mem_internalVertices _).mpr ?_, hi⟩
    refine ⟨⟨i, rfl⟩, ?_, ?_⟩
    · intro h; exact hs (hi.symm.trans (congrArg (representative index) h))
    · intro h; exact ht (hi.symm.trans (congrArg (representative index) h))
  · intro ha
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨⟨i, hi⟩, hs, ht⟩ := (p.mem_internalVertices v).mp hv
    apply (SimplePath.mem_internalVertices _ _).mpr
    exact ⟨⟨i, congrArg (representative index) hi⟩,
      fun h => hs (congrArg Sigma.fst h), fun h => ht (congrArg Sigma.fst h)⟩

/-- A section lift preserves the copied weight exactly. -/
theorem liftPath_weight {G : Digraph V} {copies : V → ℕ} {s t : V}
    (p : SimplePath G s t) (index : ∀ v, Fin (copies v)) (w : V → ℝ≥0) :
    (liftPath p index).weight (weight copies w) = p.weight w := by
  rw [SimplePath.weight, liftPath_internalVertices, Finset.sum_image]
  · rfl
  · intro a _ b _ h
    exact representative_injective index h

/-- The projection of a clone walk is an actual original directed walk. -/
def projectWalk {G : Digraph V} {copies : V → ℕ} :
    {a b : Vertex copies} → DirectedWalk (graph G copies) a b → DirectedWalk G a.1 b.1
  | _, _, .refl a => .refl a.1
  | _, _, .cons h q => .cons h (projectWalk q)

/-- Projection forgets clone indices; repeated originals remain in the walk. -/
theorem projectWalk_vertices {G : Digraph V} {copies : V → ℕ}
    {a b : Vertex copies} (q : DirectedWalk (graph G copies) a b) :
    (projectWalk q).vertices = q.vertices.image Sigma.fst := by
  induction q with
  | refl a => simp [projectWalk, DirectedWalk.vertices]
  | cons h q ih => simp [projectWalk, DirectedWalk.vertices, ih]

/-- Loop erasure after projection yields an actual original simple path.
Its internal vertices come from clone interiors, including when the clone
path revisits the original source or target via other clones. -/
theorem project_path {G : Digraph V} {copies : V → ℕ}
    {a b : Vertex copies} (q : SimplePath (graph G copies) a b) :
    ∃ p : SimplePath G a.1 b.1,
      p.internalVertices ⊆ q.internalVertices.image Sigma.fst := by
  obtain ⟨r, hr⟩ := q.exists_directedWalk
  obtain ⟨p, hp⟩ := (projectWalk r).exists_simplePath
  refine ⟨p, ?_⟩
  intro v hv
  obtain ⟨hvp, hvs, hvt⟩ := (p.mem_internalVertices v).mp hv
  have hvr := hp ((p.mem_vertices v).mpr hvp)
  rw [projectWalk_vertices] at hvr
  obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hvr
  apply Finset.mem_image.mpr
  refine ⟨c, (q.mem_internalVertices c).mpr ?_, rfl⟩
  exact ⟨(q.mem_vertices c).mp (hr hc),
    fun he => hvs (congrArg Sigma.fst he), fun he => hvt (congrArg Sigma.fst he)⟩

/-- Nonnegative copied weights pay for every original vertex surviving loop
erasure, even when distinct clones have the same original vertex. -/
theorem project_path_weight_le {G : Digraph V} {copies : V → ℕ}
    {a b : Vertex copies} (q : SimplePath (graph G copies) a b) (w : V → ℝ≥0) :
    ∃ p : SimplePath G a.1 b.1,
      p.internalVertices ⊆ q.internalVertices.image Sigma.fst ∧
      p.weight w ≤ q.weight (weight copies w) := by
  obtain ⟨p, hp⟩ := project_path q
  refine ⟨p, hp, ?_⟩
  calc
    p.weight w ≤ ∑ v ∈ q.internalVertices.image Sigma.fst, w v :=
      Finset.sum_le_sum_of_subset hp
    _ ≤ q.weight (weight copies w) := Finset.sum_image_le_of_nonneg (fun _ _ => bot_le)

/-- Every clone endpoint pair has at least its original pair's distance. -/
theorem vertexDistance_le {G : Digraph V} {copies : V → ℕ}
    (w : V → ℝ≥0) (a b : Vertex copies) :
    vertexDistance G w a.1 b.1 ≤ vertexDistance (graph G copies) (weight copies w) a b := by
  rw [le_vertexDistance_iff]
  intro q
  obtain ⟨p, _, hp⟩ := project_path_weight_le q w
  exact (vertexDistance_le_weight w p).trans (ENNReal.coe_le_coe.mpr hp)

/-- On consistently selected endpoint representatives the distances are equal. -/
theorem vertexDistance_eq {G : Digraph V} {copies : V → ℕ}
    (index : ∀ v, Fin (copies v)) (w : V → ℝ≥0) (s t : V) :
    vertexDistance (graph G copies) (weight copies w)
      (representative index s) (representative index t) = vertexDistance G w s t := by
  apply le_antisymm _ (vertexDistance_le w _ _)
  rw [le_vertexDistance_iff]
  intro p
  have hp := vertexDistance_le_weight (weight copies w) (liftPath p index)
  rw [liftPath_weight] at hp
  exact hp

/-- All clone endpoint pairs of the prescribed original demand family. -/
def allDemands (copies : V → ℕ) (D : Set (V × V)) : Set (Vertex copies × Vertex copies) :=
  {ab | (ab.1.1, ab.2.1) ∈ D}

/-- A smaller sufficient family: one fixed endpoint representative per vertex. -/
def demands {copies : V → ℕ} (index : ∀ v, Fin (copies v)) (D : Set (V × V)) :
    Set (Vertex copies × Vertex copies) :=
  (fun st => (representative index st.1, representative index st.2)) '' D

/-- Copied weights remain fractionally feasible even for all clone pairs. -/
theorem isFractionalCut_all {G : Digraph V} {copies : V → ℕ} {D : Set (V × V)}
    (w : V → ℝ≥0) (h : IsFractionalCut G w D) :
    IsFractionalCut (graph G copies) (weight copies w) (allDemands copies D) := by
  intro a b hab
  exact (h a.1 b.1 hab).trans (vertexDistance_le w a b)

/-- Fractional feasibility is preserved exactly for fixed representatives. -/
theorem isFractionalCut_iff {G : Digraph V} {copies : V → ℕ}
    (index : ∀ v, Fin (copies v)) (w : V → ℝ≥0) (D : Set (V × V)) :
    IsFractionalCut (graph G copies) (weight copies w) (demands index D) ↔
      IsFractionalCut G w D := by
  constructor
  · intro h s t hst
    simpa only [vertexDistance_eq] using
      h (representative index s) (representative index t) ⟨(s, t), hst, rfl⟩
  · intro h a b hab
    obtain ⟨⟨s, t⟩, hst, he⟩ := hab
    have ha : representative index s = a := congrArg Prod.fst he
    have hb : representative index t = b := congrArg Prod.snd he
    subst a
    subst b
    simpa only [vertexDistance_eq] using h s t hst

variable [Fintype V]

/-- Only fully deleted fibers become vertices of the original cut. -/
def fullFibers {copies : V → ℕ} (Y : Finset (Vertex copies)) : Finset V :=
  Finset.univ.filter (fun v => ∀ i : Fin (copies v), (⟨v, i⟩ : Vertex copies) ∈ Y)

@[simp] theorem mem_fullFibers {copies : V → ℕ} (Y : Finset (Vertex copies)) (v : V) :
    v ∈ fullFibers Y ↔ ∀ i : Fin (copies v), (⟨v, i⟩ : Vertex copies) ∈ Y := by
  simp [fullFibers]

/-- An avoiding original path lifts through surviving internal clones while
keeping its prescribed endpoints, even if either endpoint clone is in `Y`. -/
theorem lift_avoiding {G : Digraph V} {copies : V → ℕ} {s t : V}
    (index : ∀ v, Fin (copies v)) (Y : Finset (Vertex copies))
    (p : SimplePath G s t) (hp : p.Avoids (fullFibers Y)) :
    ∃ q : SimplePath (graph G copies) (representative index s) (representative index t),
      q.Avoids Y := by
  have hex : ∀ v, v ∉ fullFibers Y → ∃ i : Fin (copies v), (⟨v, i⟩ : Vertex copies) ∉ Y := by
    intro v hv
    simpa only [mem_fullFibers, not_forall] using hv
  let chosen : ∀ v, Fin (copies v) := fun v =>
    if v = s ∨ v = t then index v
    else if hv : v ∉ fullFibers Y then Classical.choose (hex v hv) else index v
  have hs : representative chosen s = representative index s := by simp [representative, chosen]
  have ht : representative chosen t = representative index t := by simp [representative, chosen]
  have hq : (liftPath p chosen).Avoids Y := by
    intro a ha
    rw [liftPath_internalVertices] at ha
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨_, hvs, hvt⟩ := (p.mem_internalVertices v).mp hv
    have hvY := hp v hv
    change (⟨v, chosen v⟩ : Vertex copies) ∉ Y
    simpa only [chosen, ite_eq_right (not_or.mpr ⟨hvs, hvt⟩), dite_eq_left hvY] using
      Classical.choose_spec (hex v hvY)
  have h : ∃ q : SimplePath (graph G copies) (representative chosen s) (representative chosen t),
      q.Avoids Y := ⟨liftPath p chosen, hq⟩
  rw [hs, ht] at h
  exact h

/-- Any clone cut for fixed endpoint representatives pulls back via full fibers. -/
theorem cutsPair_pullback {G : Digraph V} {copies : V → ℕ} {s t : V}
    (index : ∀ v, Fin (copies v)) (Y : Finset (Vertex copies))
    (h : CutsPair (graph G copies) Y (representative index s) (representative index t)) :
    CutsPair G (fullFibers Y) s t := by
  by_contra hn
  obtain ⟨p, hp⟩ := (not_cutsPair_iff G (fullFibers Y) s t).mp hn
  obtain ⟨q, hq⟩ := lift_avoiding index Y p hp
  obtain ⟨a, ha, haY⟩ := h q
  exact hq a ha haY

/-- Demand-preserving integral pullback requires only the fixed representatives. -/
theorem isIntegralCut_pullback {G : Digraph V} {copies : V → ℕ} {D : Set (V × V)}
    (index : ∀ v, Fin (copies v)) (Y : Finset (Vertex copies))
    (h : IsIntegralCut (graph G copies) Y (demands index D)) :
    IsIntegralCut G (fullFibers Y) D := by
  intro s t hst
  exact cutsPair_pullback index Y
    (h (representative index s) (representative index t) ⟨(s, t), hst, rfl⟩)

/-- In particular a cut for every threshold demand in the replicated graph
pulls back to a cut for every original threshold demand. -/
theorem threshold_cut_pullback {G : Digraph V} {copies : V → ℕ}
    (index : ∀ v, Fin (copies v)) (w : V → ℝ≥0) (Y : Finset (Vertex copies))
    (h : IsIntegralCut (graph G copies) Y (thresholdDemands (graph G copies) (weight copies w))) :
    IsIntegralCut G (fullFibers Y) (thresholdDemands G w) := by
  intro s t hst
  apply cutsPair_pullback index Y
  apply h
  change 1 ≤ vertexDistance (graph G copies) (weight copies w)
    (representative index s) (representative index t)
  rw [vertexDistance_eq]
  exact hst

omit [DecidableEq V] in
/-- There are exactly as many clone vertices as the sum of the fiber sizes. -/
@[simp] theorem card_vertex (copies : V → ℕ) :
    Fintype.card (Vertex copies) = ∑ v, copies v := by
  simp [Vertex, Fintype.card_sigma]

omit [DecidableEq V] in
/-- Exact accounting of total copied weight. -/
@[simp] theorem totalWeight_weight (copies : V → ℕ) (w : V → ℝ≥0) :
    totalWeight (weight copies w) = ∑ v, (copies v : ℝ≥0) * w v := by
  simp [totalWeight, weight, Fintype.sum_sigma, nsmul_eq_mul]

omit [DecidableEq V] in
/-- The unit-cost fractional objective is the total copied weight. -/
@[simp] theorem weightedCost_weight (copies : V → ℕ) (w : V → ℝ≥0) :
    weightedCost (cost copies) (weight copies w) = ∑ v, (copies v : ℝ≥0) * w v := by
  unfold cost
  rw [weightedCost_unit, totalWeight_weight]

/-- Counting all clones in fully deleted fibers never overcounts a clone cut. -/
theorem sum_fullFibers_le_card {copies : V → ℕ} (Y : Finset (Vertex copies)) :
    (∑ v ∈ fullFibers Y, copies v) ≤ Y.card := by
  have hsub : (fullFibers Y).sigma (fun v => (Finset.univ : Finset (Fin (copies v)))) ⊆ Y := by
    intro a ha
    obtain ⟨ha, _⟩ := Finset.mem_sigma.mp ha
    exact (mem_fullFibers Y a.1).mp ha a.2
  have hc := Finset.card_le_card hsub
  simpa only [Finset.card_sigma, Finset.card_univ, Fintype.card_fin] using hc

/-- If replication covers original costs, every clone cut pays for its full
fiber pullback. A partially deleted fiber contributes no original cost. -/
theorem cutCost_fullFibers_le_card {copies : V → ℕ} (originalCost : V → ℝ≥0)
    (hcost : ∀ v, originalCost v ≤ copies v) (Y : Finset (Vertex copies)) :
    cutCost originalCost (fullFibers Y) ≤ (Y.card : ℝ≥0) := by
  calc
    cutCost originalCost (fullFibers Y) ≤ ∑ v ∈ fullFibers Y, (copies v : ℝ≥0) :=
      Finset.sum_le_sum (fun v _ => hcost v)
    _ ≤ (Y.card : ℝ≥0) := by exact_mod_cast sum_fullFibers_le_card Y

/-- The previous bound is exactly the objective bound against unit clone costs. -/
theorem cutCost_pullback {copies : V → ℕ} (originalCost : V → ℝ≥0)
    (hcost : ∀ v, originalCost v ≤ copies v) (Y : Finset (Vertex copies)) :
    cutCost originalCost (fullFibers Y) ≤ cutCost (cost copies) Y := by
  unfold cost
  rw [cutCost_unit]
  exact cutCost_fullFibers_le_card originalCost hcost Y

omit [Fintype V] in
/-- Explicit composition with the contraction repair: all original demands
retain their permanent source/sink ports and their fixed clone representatives. -/
theorem port_isFractionalCut_double {G : Digraph V} {S : Finset V} {D : Set (V × V)}
    (copies : ShortcutContraction.Survivor (S.image TerminalPorts.core) → ℕ)
    (index : ∀ v, Fin (copies v)) (w : V → ℝ≥0)
    (hmass : (∑ v ∈ S, w v) ≤ (1 / 2 : ℝ≥0)) (h : IsFractionalCut G w D) :
    IsFractionalCut
      (graph (ShortcutContraction.graph (TerminalPorts.graph G) (S.image TerminalPorts.core)) copies)
      (weight copies (fun v => 2 * TerminalPorts.extend w v.val))
      (demands index (ShortcutContraction.portDemands S D)) := by
  apply (isFractionalCut_iff index _ _).mpr
  exact ShortcutContraction.port_isFractionalCut_double w hmass h

/-- Full-fiber pullback, shortcut pullback, and core pullback compose without
losing demand endpoints, including demands whose original cores were removed. -/
theorem port_isIntegralCut_pullback {G : Digraph V} {S : Finset V} {D : Set (V × V)}
    {copies : ShortcutContraction.Survivor (S.image TerminalPorts.core) → ℕ}
    (index : ∀ v, Fin (copies v)) (Y : Finset (Vertex copies))
    (h : IsIntegralCut
      (graph (ShortcutContraction.graph (TerminalPorts.graph G) (S.image TerminalPorts.core)) copies)
      Y (demands index (ShortcutContraction.portDemands S D))) :
    IsIntegralCut G (TerminalPorts.corePreimage ((fullFibers Y).image Subtype.val)) D := by
  exact ShortcutContraction.port_isIntegralCut_pullback (fullFibers Y)
    (isIntegralCut_pullback index Y h)

/-- The composed original cut is paid for by unit-cost deleted clones; zero-cost
permanent ports need no positive original-cost assumption. -/
theorem port_cutCost_pullback {S : Finset V}
    {copies : ShortcutContraction.Survivor (S.image TerminalPorts.core) → ℕ}
    (originalCost : V → ℝ≥0)
    (hcost : ∀ v, TerminalPorts.extend originalCost v.val ≤ copies v)
    (Y : Finset (Vertex copies)) :
    cutCost originalCost (TerminalPorts.corePreimage ((fullFibers Y).image Subtype.val)) ≤
      (Y.card : ℝ≥0) := by
  rw [ShortcutContraction.port_cutCost_pullback]
  exact cutCost_fullFibers_le_card (fun v => TerminalPorts.extend originalCost v.val) hcost Y

end VertexReplication

end

end DirectedFlowCutGap
