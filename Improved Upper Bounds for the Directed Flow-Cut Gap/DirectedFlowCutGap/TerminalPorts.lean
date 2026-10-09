import DirectedFlowCutGap.PathExtraction

/-!
# Permanent source and sink representatives

Replace every original vertex by a weighted core, a zero-weight source port,
and a zero-weight sink port. This construction preserves endpoint-excluding
vertex distances, cut feasibility, total weight, and the fractional objective.
Projected paths may revisit an original endpoint through its core; projection
therefore produces an actual walk and uses the proved loop-erasure theorem.

This is a foundational repair component for the endpoint issues in Lemma 18
and Theorem 29 of arXiv:2604.03412v3. It does not assert either the full witness
lemma or the subsequent low-weight contraction and unit-cost reduction.
-/

namespace DirectedFlowCutGap

noncomputable section

open scoped BigOperators NNReal ENNReal

namespace TerminalPorts

variable {V : Type*}

/-- One core and two permanent terminal representatives per original vertex. -/
abbrev Vertex (V : Type*) := V ⊕ (V ⊕ V)

abbrev core (v : V) : Vertex V := Sum.inl v
abbrev source (v : V) : Vertex V := Sum.inr (Sum.inl v)
abbrev sink (v : V) : Vertex V := Sum.inr (Sum.inr v)

/-- Forget the role of a representative. This is not injective. -/
def original : Vertex V → V
  | .inl v => v
  | .inr (.inl v) => v
  | .inr (.inr v) => v

/-- The direct self port edge represents the original length-zero path. -/
def graph (G : Digraph V) : Digraph (Vertex V) where
  Adj
    | .inl u, .inl v => G.Adj u v
    | .inr (.inl u), .inl v => G.Adj u v
    | .inl u, .inr (.inr v) => G.Adj u v
    | .inr (.inl u), .inr (.inr v) => u = v ∨ G.Adj u v
    | _, _ => False

/-- Put the original weight or cost on cores and zero on ports. -/
def extend (w : V → ℝ≥0) : Vertex V → ℝ≥0
  | .inl v => w v
  | .inr _ => 0

@[simp] theorem extend_core (w : V → ℝ≥0) (v : V) : extend w (core v) = w v := rfl
@[simp] theorem extend_source (w : V → ℝ≥0) (v : V) : extend w (source v) = 0 := rfl
@[simp] theorem extend_sink (w : V → ℝ≥0) (v : V) : extend w (sink v) = 0 := rfl

@[simp] theorem no_incoming_source (G : Digraph V) (x : Vertex V) (v : V) :
    ¬(graph G).Adj x (source v) := by
  cases x with
  | inl u => exact id
  | inr x => cases x <;> exact id

@[simp] theorem no_outgoing_sink (G : Digraph V) (v : V) (x : Vertex V) :
    ¬(graph G).Adj (sink v) x := by
  cases x with
  | inl u => exact id
  | inr x => cases x <;> exact id

variable [DecidableEq V]

private theorem not_internal_of_no_incoming {A : Type*} [DecidableEq A]
    {H : Digraph A} {a b x : A} (p : SimplePath H a b)
    (hx : ∀ y, ¬H.Adj y x) : x ∉ p.internalVertices := by
  intro h
  obtain ⟨⟨i, hi⟩, hxa, _hxb⟩ := (p.mem_internalVertices x).mp h
  have hpos : 0 < i.val := by
    by_contra hn
    have iz : i = 0 := by
      apply Fin.ext
      change i.val = 0
      omega
    exact hxa (hi.symm.trans ((congrArg p.vertex iz).trans p.source_eq))
  let j : Fin p.edgeLength := ⟨i.val - 1, by omega⟩
  have hj : j.succ = i := Fin.ext (by dsimp [j]; omega)
  have he := p.adjacent j
  rw [hj, hi] at he
  exact hx _ he

private theorem not_internal_of_no_outgoing {A : Type*} [DecidableEq A]
    {H : Digraph A} {a b x : A} (p : SimplePath H a b)
    (hx : ∀ y, ¬H.Adj x y) : x ∉ p.internalVertices := by
  intro h
  obtain ⟨⟨i, hi⟩, _hxa, hxb⟩ := (p.mem_internalVertices x).mp h
  have hlt : i.val < p.edgeLength := by
    by_contra hn
    have iz : i = Fin.last p.edgeLength := Fin.ext (by simp; omega)
    exact hxb (hi.symm.trans ((congrArg p.vertex iz).trans p.target_eq))
  let j : Fin p.edgeLength := ⟨i.val, hlt⟩
  have hj : j.castSucc = i := Fin.ext rfl
  have he := p.adjacent j
  rw [hj, hi] at he
  exact hx _ he

/-- No source port can occur internally on any simple path, for any endpoints. -/
theorem source_not_internal {G : Digraph V} {a b : Vertex V}
    (p : SimplePath (graph G) a b) (v : V) : source v ∉ p.internalVertices :=
  not_internal_of_no_incoming p (fun x => no_incoming_source G x v)

/-- No sink port can occur internally on any simple path, for any endpoints. -/
theorem sink_not_internal {G : Digraph V} {a b : Vertex V}
    (p : SimplePath (graph G) a b) (v : V) : sink v ∉ p.internalVertices :=
  not_internal_of_no_outgoing p (fun x => no_outgoing_sink G v x)

/-- Only cores can help cut a path, even when the path endpoints are not ports. -/
theorem internal_is_core {G : Digraph V} {a b : Vertex V}
    (p : SimplePath (graph G) a b) {x : Vertex V} (hx : x ∈ p.internalVertices) :
    ∃ v, core v = x := by
  cases x with
  | inl v => exact ⟨v, rfl⟩
  | inr x =>
    cases x with
    | inl v => exact (source_not_internal p v hx).elim
    | inr v => exact (sink_not_internal p v hx).elim

private def liftVertex {G : Digraph V} {s t : V} (p : SimplePath G s t)
    (i : Fin (p.edgeLength + 1)) : Vertex V :=
  if i.val = 0 then source (p.vertex i)
  else if i.val = p.edgeLength then sink (p.vertex i)
  else core (p.vertex i)

omit [DecidableEq V] in
private theorem original_liftVertex {G : Digraph V} {s t : V}
    (p : SimplePath G s t) (i : Fin (p.edgeLength + 1)) :
    original (liftVertex p i) = p.vertex i := by
  unfold liftVertex
  split_ifs <;> rfl

/-- A positive-length original simple path replaces its two endpoints by ports. -/
def liftPositive {G : Digraph V} {s t : V} (p : SimplePath G s t)
    (hn : 0 < p.edgeLength) : SimplePath (graph G) (source s) (sink t) where
  edgeLength := p.edgeLength
  vertex := liftVertex p
  source_eq := by simp [liftVertex, p.source_eq]
  target_eq := by simp [liftVertex, Nat.ne_of_gt hn, p.target_eq]
  injective := by
    intro i j hij
    apply p.injective
    simpa only [original_liftVertex] using congrArg original hij
  adjacent := by
    intro i
    have hi := i.isLt
    have he := p.adjacent i
    simp only [liftVertex, Fin.val_castSucc, Fin.val_succ]
    split_ifs <;> simp_all [graph]

/-- The lift preserves the internal vertex set exactly, with a core tag. -/
theorem liftPositive_internalVertices {G : Digraph V} {s t : V}
    (p : SimplePath G s t) (hn : 0 < p.edgeLength) :
    (liftPositive p hn).internalVertices = p.internalVertices.image core := by
  ext x
  constructor
  · intro hx
    obtain ⟨v, rfl⟩ := internal_is_core (liftPositive p hn) hx
    obtain ⟨⟨i, hi⟩, _, _⟩ := ((liftPositive p hn).mem_internalVertices (core v)).mp hx
    change liftVertex p i = core v at hi
    have hiz : i.val ≠ 0 := by
      intro he
      simp [liftVertex, he] at hi
    have hin : i.val ≠ p.edgeLength := by
      intro he
      simp [liftVertex, he, Nat.ne_of_gt hn] at hi
    have hiv : p.vertex i = v := by simpa [liftVertex, hiz, hin] using hi
    apply Finset.mem_image.mpr
    refine ⟨v, (p.mem_internalVertices v).mpr ⟨⟨i, hiv⟩, ?_, ?_⟩, rfl⟩
    · intro hvs
      have : i = 0 := p.injective (hiv.trans (hvs.trans p.source_eq.symm))
      exact hiz (congrArg Fin.val this)
    · intro hvt
      have : i = Fin.last p.edgeLength :=
        p.injective (hiv.trans (hvt.trans p.target_eq.symm))
      exact hin (congrArg Fin.val this)
  · intro hx
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨⟨i, hi⟩, hvs, hvt⟩ := (p.mem_internalVertices v).mp hv
    have hiz : i.val ≠ 0 := by
      intro he
      have : i = 0 := Fin.ext he
      exact hvs (hi.symm.trans ((congrArg p.vertex this).trans p.source_eq))
    have hin : i.val ≠ p.edgeLength := by
      intro he
      have : i = Fin.last p.edgeLength := Fin.ext he
      exact hvt (hi.symm.trans ((congrArg p.vertex this).trans p.target_eq))
    apply ((liftPositive p hn).mem_internalVertices (core v)).mpr
    exact ⟨⟨i, by simp [liftPositive, liftVertex, hiz, hin, hi]⟩, by simp, by simp⟩

/-- Original simple paths lift exactly, including the length-zero self path. -/
theorem exists_lift {G : Digraph V} {s t : V} (p : SimplePath G s t) :
    ∃ q : SimplePath (graph G) (source s) (sink t),
      q.internalVertices = p.internalVertices.image core := by
  by_cases hn : 0 < p.edgeLength
  · exact ⟨liftPositive p hn, liftPositive_internalVertices p hn⟩
  · have hz : p.edgeLength = 0 := by omega
    have hst : s = t := by
      have hi : (0 : Fin (p.edgeLength + 1)) = Fin.last p.edgeLength :=
        Fin.ext (by simp [hz])
      exact p.source_eq.symm.trans ((congrArg p.vertex hi).trans p.target_eq)
    have hp : p.internalVertices = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro v hv
      obtain ⟨⟨i, hi⟩, hs, _⟩ := (p.mem_internalVertices v).mp hv
      have hi0 : i = 0 := Fin.ext (by have := i.isLt; simp [hz] at this; omega)
      exact hs (hi.symm.trans ((congrArg p.vertex hi0).trans p.source_eq))
    refine ⟨SimplePath.edge (G := graph G) (Or.inl hst) (by simp), ?_⟩
    rw [hp, Finset.image_empty]
    exact SimplePath.edge_internalVertices _ _

/-- Exact cost of any finite collection of core representatives. -/
theorem sum_extend_image (w : V → ℝ≥0) (X : Finset V) :
    ∑ x ∈ X.image core, extend w x = ∑ v ∈ X, w v := by
  rw [Finset.sum_image]
  · rfl
  · intro a _ b _ h
    exact Sum.inl.inj h

theorem exists_lift_weight {G : Digraph V} {s t : V}
    (p : SimplePath G s t) (w : V → ℝ≥0) :
    ∃ q : SimplePath (graph G) (source s) (sink t),
      q.internalVertices = p.internalVertices.image core ∧ q.weight (extend w) = p.weight w := by
  obtain ⟨q, hq⟩ := exists_lift p
  refine ⟨q, hq, ?_⟩
  simp only [SimplePath.weight, hq, sum_extend_image]

private def reflexiveGraph (G : Digraph V) : Digraph V where
  Adj u v := u = v ∨ G.Adj u v

omit [DecidableEq V] in
private theorem projection_adj {G : Digraph V} {a b : Vertex V}
    (h : (graph G).Adj a b) : (reflexiveGraph G).Adj (original a) (original b) := by
  cases a with
  | inl u =>
    cases b with
    | inl v => exact Or.inr h
    | inr b => cases b with
      | inl v => exact h.elim
      | inr v => exact Or.inr h
  | inr a =>
    cases a with
    | inl u =>
      cases b with
      | inl v => exact Or.inr h
      | inr b => cases b with
        | inl v => exact h.elim
        | inr v => exact h
    | inr u => exact (no_outgoing_sink G u b h).elim

private def projectWalk {G : Digraph V} {a b : Vertex V}
    (q : DirectedWalk (graph G) a b) : DirectedWalk (reflexiveGraph G) (original a) (original b) :=
  match q with
  | .refl a => .refl (original a)
  | .cons h q => .cons (projection_adj h) (projectWalk q)

private theorem projectWalk_vertices {G : Digraph V} {a b : Vertex V}
    (q : DirectedWalk (graph G) a b) :
    (projectWalk q).vertices = q.vertices.image original := by
  induction q with
  | refl a => simp [projectWalk, DirectedWalk.vertices]
  | cons h q ih => simp [projectWalk, DirectedWalk.vertices, ih]

/-- Removing only reflexive steps still leaves a real directed walk. -/
private theorem erase_reflexive_steps {G : Digraph V} {s t : V}
    (q : DirectedWalk (reflexiveGraph G) s t) :
    ∃ p : DirectedWalk G s t, p.vertices ⊆ q.vertices := by
  induction q with
  | refl s => exact ⟨.refl s, Finset.Subset.refl _⟩
  | @cons s u t h q ih =>
    obtain ⟨p, hp⟩ := ih
    rcases h with he | he
    · subst u
      exact ⟨p, hp.trans (Finset.subset_insert _ _)⟩
    · exact ⟨.cons he p, Finset.insert_subset_insert _ hp⟩

/-- Projection plus genuine loop erasure, with all original internal vertices
represented by internal cores of the given port path. -/
theorem exists_projection {G : Digraph V} {s t : V}
    (q : SimplePath (graph G) (source s) (sink t)) :
    ∃ p : SimplePath G s t, p.internalVertices.image core ⊆ q.internalVertices := by
  obtain ⟨a, ha⟩ := q.exists_directedWalk
  obtain ⟨b, hb⟩ := erase_reflexive_steps (projectWalk a)
  obtain ⟨p, hp⟩ := b.exists_simplePath
  refine ⟨p, ?_⟩
  intro x hx
  obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hx
  obtain ⟨hvp, hvs, hvt⟩ := (p.mem_internalVertices v).mp hv
  have hvm : v ∈ (projectWalk a).vertices := hb (hp ((p.mem_vertices v).mpr hvp))
  rw [projectWalk_vertices] at hvm
  obtain ⟨y, hy, hyv⟩ := Finset.mem_image.mp hvm
  have hyq := ha hy
  have hys : y ≠ source s := by
    intro he
    subst y
    exact hvs hyv.symm
  have hyt : y ≠ sink t := by
    intro he
    subst y
    exact hvt hyv.symm
  have hyint : y ∈ q.internalVertices :=
    (q.mem_internalVertices y).mpr ⟨(q.mem_vertices y).mp hyq, hys, hyt⟩
  obtain ⟨u, rfl⟩ := internal_is_core q hyint
  change u = v at hyv
  simpa only [hyv] using hyint

/-- Endpoint cores, if present, are charged in the port path; erasing loops and
removing original endpoints can only decrease a nonnegative path weight. -/
theorem exists_projection_weight_le {G : Digraph V} {s t : V}
    (q : SimplePath (graph G) (source s) (sink t)) (w : V → ℝ≥0) :
    ∃ p : SimplePath G s t, p.internalVertices.image core ⊆ q.internalVertices ∧
      p.weight w ≤ q.weight (extend w) := by
  obtain ⟨p, hp⟩ := exists_projection q
  refine ⟨p, hp, ?_⟩
  change (∑ v ∈ p.internalVertices, w v) ≤ ∑ x ∈ q.internalVertices, extend w x
  rw [← sum_extend_image w p.internalVertices]
  exact Finset.sum_le_sum_of_subset hp

/-- Exact extended distance, including self pairs and unreachable pairs. -/
theorem vertexDistance_eq (G : Digraph V) (w : V → ℝ≥0) (s t : V) :
    vertexDistance (graph G) (extend w) (source s) (sink t) = vertexDistance G w s t := by
  apply le_antisymm
  · rw [le_vertexDistance_iff]
    intro p
    obtain ⟨q, _, hq⟩ := exists_lift_weight p w
    simpa only [hq] using vertexDistance_le_weight (extend w) q
  · rw [le_vertexDistance_iff]
    intro q
    obtain ⟨p, _, hp⟩ := exists_projection_weight_le q w
    exact (vertexDistance_le_weight w p).trans (ENNReal.coe_le_coe.mpr hp)

/-- Pull a cut back through the injective core map, discarding all ports. -/
def corePreimage (Y : Finset (Vertex V)) : Finset V :=
  Y.preimage core (fun _ _ _ _ h => Sum.inl.inj h)

omit [DecidableEq V] in
@[simp] theorem mem_corePreimage (Y : Finset (Vertex V)) (v : V) :
    v ∈ corePreimage Y ↔ core v ∈ Y := Finset.mem_preimage

@[simp] theorem corePreimage_image (X : Finset V) :
    corePreimage (X.image core) = X := by
  ext v
  simp [mem_corePreimage]

/-- Ports never help a cut, for arbitrary path endpoints. -/
theorem cutsPair_core_only_iff (G : Digraph V) (Y : Finset (Vertex V)) (a b : Vertex V) :
    CutsPair (graph G) ((corePreimage Y).image core) a b ↔ CutsPair (graph G) Y a b := by
  constructor
  · intro h p
    obtain ⟨x, hx, hxy⟩ := h p
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hxy
    exact ⟨core v, hx, (mem_corePreimage Y v).mp hv⟩
  · intro h p
    obtain ⟨x, hx, hxy⟩ := h p
    obtain ⟨v, rfl⟩ := internal_is_core p hx
    exact ⟨core v, hx, Finset.mem_image.mpr ⟨v, (mem_corePreimage Y v).mpr hxy, rfl⟩⟩

/-- Exact cut transfer at permanent demand ports. -/
theorem cutsPair_iff (G : Digraph V) (Y : Finset (Vertex V)) (s t : V) :
    CutsPair (graph G) Y (source s) (sink t) ↔ CutsPair G (corePreimage Y) s t := by
  constructor
  · intro h p
    obtain ⟨q, hq⟩ := exists_lift p
    obtain ⟨x, hx, hxy⟩ := h q
    rw [hq] at hx
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hx
    exact ⟨v, hv, (mem_corePreimage Y v).mpr hxy⟩
  · intro h q
    obtain ⟨p, hp⟩ := exists_projection q
    obtain ⟨v, hv, hvy⟩ := h p
    exact ⟨core v, hp (Finset.mem_image.mpr ⟨v, hv, rfl⟩),
      (mem_corePreimage Y v).mp hvy⟩

/-- An original cut lifts to its core representatives, with exact feasibility. -/
theorem cutsPair_image_iff (G : Digraph V) (X : Finset V) (s t : V) :
    CutsPair (graph G) (X.image core) (source s) (sink t) ↔ CutsPair G X s t := by
  rw [cutsPair_iff, corePreimage_image]

/-- Demand pairs retain permanent distinct source and sink representatives. -/
def demands (D : Set (V × V)) : Set (Vertex V × Vertex V) :=
  (fun st => (source st.1, sink st.2)) '' D

/-- Fractional feasibility is preserved for any explicitly chosen demand family. -/
theorem isFractionalCut_iff (G : Digraph V) (w : V → ℝ≥0) (D : Set (V × V)) :
    IsFractionalCut (graph G) (extend w) (demands D) ↔ IsFractionalCut G w D := by
  constructor
  · intro h s t hst
    have hh := h (source s) (sink t) ⟨(s, t), hst, rfl⟩
    simpa only [vertexDistance_eq] using hh
  · intro h a b hab
    obtain ⟨⟨s, t⟩, hst, he⟩ := hab
    have ha : source s = a := congrArg Prod.fst he
    have hb : sink t = b := congrArg Prod.snd he
    subst a
    subst b
    simpa only [vertexDistance_eq] using h s t hst

/-- Integral feasibility pulls back through cores for any demand family. -/
theorem isIntegralCut_iff (G : Digraph V) (Y : Finset (Vertex V)) (D : Set (V × V)) :
    IsIntegralCut (graph G) Y (demands D) ↔ IsIntegralCut G (corePreimage Y) D := by
  constructor
  · intro h s t hst
    exact (cutsPair_iff G Y s t).mp (h (source s) (sink t) ⟨(s, t), hst, rfl⟩)
  · intro h a b hab
    obtain ⟨⟨s, t⟩, hst, he⟩ := hab
    have ha : source s = a := congrArg Prod.fst he
    have hb : sink t = b := congrArg Prod.snd he
    subst a
    subst b
    exact (cutsPair_iff G Y s t).mpr (h s t hst)

/-- Zero-cost ports make cut pullback preserve cost exactly. -/
theorem cutCost_corePreimage (cost : V → ℝ≥0) (Y : Finset (Vertex V)) :
    cutCost cost (corePreimage Y) = cutCost (extend cost) Y := by
  classical
  rw [cutCost, ← sum_extend_image]
  apply Finset.sum_subset
  · intro x hx
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hx
    exact (mem_corePreimage Y v).mp hv
  · intro x hx hnot
    cases x with
    | inl v =>
      exact (hnot (Finset.mem_image.mpr ⟨v, (mem_corePreimage Y v).mpr hx, rfl⟩)).elim
    | inr x => rfl

variable [Fintype V]

omit [DecidableEq V] in
/-- Exactly three vertices per original vertex, including when `V` is empty. -/
@[simp] theorem card_vertex : Fintype.card (Vertex V) = 3 * Fintype.card V := by
  simp only [Vertex, Fintype.card_sum]
  omega

omit [DecidableEq V] in
@[simp] theorem totalWeight_extend (w : V → ℝ≥0) :
    totalWeight (extend w) = totalWeight w := by
  simp [totalWeight, Fintype.sum_sum_type, extend]

omit [DecidableEq V] in
@[simp] theorem weightedCost_extend (cost w : V → ℝ≥0) :
    weightedCost (extend cost) (extend w) = weightedCost cost w := by
  simp [weightedCost, Fintype.sum_sum_type, extend]

end TerminalPorts

end

end DirectedFlowCutGap
