import DirectedFlowCutGap.Basic

/-!
# Finite attainment and directed walk extraction

Actual directed walks admit simple paths with the same endpoints and contained
vertex support. This supplies composition without assuming either a simple
replacement or a distance triangle inequality. The vertex-distance composition
bound charges the common endpoint once, because path weights exclude endpoints.
-/

namespace DirectedFlowCutGap

noncomputable section

open scoped BigOperators NNReal ENNReal

variable {V : Type*} [DecidableEq V]

namespace SimplePath

variable {G : Digraph V} {s u t : V}

/-- A finite code retains the path length and every vertex in order. -/
def finiteCode [Fintype V] (p : SimplePath G s t) :
    Σ n : Fin (Fintype.card V), Fin (n.val + 1) → V :=
  ⟨⟨p.edgeLength, p.edgeLength_lt_card⟩, p.vertex⟩

theorem finiteCode_injective [Fintype V] :
    Function.Injective (finiteCode : SimplePath G s t → _) := by
  intro p q h
  have hn : p.edgeLength = q.edgeLength := congrArg (fun x => x.1.val) h
  cases p with
  | mk n v hs ht hi ha =>
    cases q with
    | mk m z ks kt ki ka =>
      dsimp only at hn
      subst m
      have hv : v = z := eq_of_heq (Sigma.mk.inj_iff.mp h).2
      subst z
      rfl

instance finite [Fintype V] : Finite (SimplePath G s t) :=
  Finite.of_injective finiteCode finiteCode_injective

/-- Keep the suffix starting at an actual occurrence of a vertex. -/
def suffix (p : SimplePath G s t) (i : Fin (p.edgeLength + 1)) :
    SimplePath G (p.vertex i) t where
  edgeLength := p.edgeLength - i.val
  vertex j := p.vertex ⟨i.val + j.val, by omega⟩
  source_eq := by congr 1
  target_eq := by
    convert p.target_eq using 1
    congr 1
    apply Fin.ext
    dsimp
    omega
  injective := by
    intro j k h
    have hh := congrArg Fin.val (p.injective h)
    apply Fin.ext
    dsimp at hh
    omega
  adjacent := by
    intro j
    exact p.adjacent ⟨i.val + j.val, by omega⟩

theorem suffix_vertices_subset (p : SimplePath G s t)
    (i : Fin (p.edgeLength + 1)) : (p.suffix i).vertices ⊆ p.vertices := by
  intro v hv
  obtain ⟨j, rfl⟩ := ((p.suffix i).mem_vertices v).mp hv
  exact (p.mem_vertices _).mpr ⟨⟨i.val + j.val, by
    have hj := j.isLt
    change j.val < p.edgeLength - i.val + 1 at hj
    omega⟩, rfl⟩

/-- Prepend a directed edge when the new source is absent from the old path. -/
def prepend (p : SimplePath G u t) (h : G.Adj s u) (hs : s ∉ p.vertices) :
    SimplePath G s t where
  edgeLength := p.edgeLength + 1
  vertex := Fin.cases s p.vertex
  source_eq := rfl
  target_eq := by
    simpa only [← Fin.succ_last, Fin.cases_succ] using p.target_eq
  injective := by
    intro i j hij
    cases i using Fin.cases with
    | zero =>
      cases j using Fin.cases with
      | zero => rfl
      | succ j =>
        exact (hs ((p.mem_vertices s).mpr ⟨j, hij.symm⟩)).elim
    | succ i =>
      cases j using Fin.cases with
      | zero =>
        exact (hs ((p.mem_vertices s).mpr ⟨i, hij⟩)).elim
      | succ j => exact congrArg Fin.succ (p.injective hij)
  adjacent := by
    intro i
    cases i using Fin.cases with
    | zero => simpa only [Fin.castSucc_zero, Fin.cases_zero, Fin.cases_succ, p.source_eq] using h
    | succ i => exact p.adjacent i

theorem prepend_vertices (p : SimplePath G u t) (h : G.Adj s u)
    (hs : s ∉ p.vertices) : (p.prepend h hs).vertices = insert s p.vertices := by
  ext v
  simp only [mem_vertices, Finset.mem_insert]
  constructor
  · rintro ⟨i, hi⟩
    cases i using Fin.cases with
    | zero => exact Or.inl hi.symm
    | succ i => exact Or.inr ⟨i, hi⟩
  · rintro (rfl | ⟨i, hi⟩)
    · exact ⟨0, rfl⟩
    · exact ⟨i.succ, hi⟩

end SimplePath

/-- A concrete finite directed walk. Repeated vertices and self-loops are allowed. -/
inductive DirectedWalk (G : Digraph V) : V → V → Type _
  | refl (s : V) : DirectedWalk G s s
  | cons {s u t : V} (edge : G.Adj s u) (tail : DirectedWalk G u t) :
      DirectedWalk G s t

namespace DirectedWalk

variable {G : Digraph V} {s u t : V}

/-- Support includes both endpoints, irrespective of repetitions. -/
def vertices : {s t : V} → DirectedWalk G s t → Finset V
  | s, _, .refl _ => {s}
  | s, _, .cons _ q => insert s q.vertices

/-- Concatenate actual directed walks at their common endpoint. -/
def append : {s u t : V} → DirectedWalk G s u → DirectedWalk G u t → DirectedWalk G s t
  | _, _, _, .refl _, q => q
  | _, _, _, .cons h p, q => .cons h (p.append q)

theorem source_mem_vertices (q : DirectedWalk G s t) : s ∈ q.vertices := by
  cases q <;> simp [vertices]

theorem append_vertices (p : DirectedWalk G s u) (q : DirectedWalk G u t) :
    (p.append q).vertices = p.vertices ∪ q.vertices := by
  induction p with
  | refl => simp [append, vertices, q.source_mem_vertices]
  | cons h p ih => simp [append, vertices, ih, Finset.insert_union]

/-- Loop erasure: every directed walk has a simple path with contained support. -/
theorem exists_simplePath (q : DirectedWalk G s t) :
    ∃ p : SimplePath G s t, p.vertices ⊆ q.vertices := by
  induction q with
  | refl s =>
    refine ⟨SimplePath.refl G s, ?_⟩
    intro v hv
    obtain ⟨i, rfl⟩ := (SimplePath.mem_vertices _ _).mp hv
    simp [SimplePath.refl, vertices]
  | @cons s u t h q ih =>
    obtain ⟨p, hp⟩ := ih
    by_cases hs : s ∈ p.vertices
    · obtain ⟨i, hi⟩ := (p.mem_vertices s).mp hs
      subst s
      exact ⟨p.suffix i, (p.suffix_vertices_subset i).trans
        (hp.trans (Finset.subset_insert _ _))⟩
    · refine ⟨p.prepend h hs, ?_⟩
      rw [p.prepend_vertices]
      exact Finset.insert_subset_insert _ hp

/-- Turn a finite sequence with every directed edge explicit into a walk. -/
theorem exists_of_sequence {n : ℕ} (v : Fin (n + 1) → V)
    (h : ∀ i : Fin n, G.Adj (v i.castSucc) (v i.succ)) :
    ∃ q : DirectedWalk G (v 0) (v (Fin.last n)),
      ∀ x ∈ q.vertices, ∃ i, v i = x := by
  induction n with
  | zero =>
    refine ⟨.refl (v 0), ?_⟩
    intro x hx
    simp only [vertices, Finset.mem_singleton] at hx
    exact ⟨0, hx.symm⟩
  | succ n ih =>
    obtain ⟨q, hq⟩ := ih (fun i => v i.succ) (fun i => h i.succ)
    refine ⟨.cons (h 0) q, ?_⟩
    intro x hx
    simp only [vertices, Finset.mem_insert] at hx
    rcases hx with rfl | hx
    · exact ⟨0, rfl⟩
    · obtain ⟨i, hi⟩ := hq x hx
      exact ⟨i.succ, hi⟩

/-- Loop erasure can only decrease the nonnegative cost of internal support. -/
theorem exists_simplePath_weight_le (q : DirectedWalk G s t) (w : V → ℝ≥0) :
    ∃ p : SimplePath G s t, p.vertices ⊆ q.vertices ∧
      p.weight w ≤ ∑ v ∈ q.vertices \ {s, t}, w v := by
  obtain ⟨p, hp⟩ := q.exists_simplePath
  refine ⟨p, hp, Finset.sum_le_sum_of_subset ?_⟩
  exact Finset.sdiff_subset_sdiff_left _ hp

end DirectedWalk

namespace SimplePath

variable {G : Digraph V} {s u t : V}

/-- Every simple path determines an actual walk with contained vertex support. -/
theorem exists_directedWalk (p : SimplePath G s t) :
    ∃ q : DirectedWalk G s t, q.vertices ⊆ p.vertices := by
  cases p with
  | mk n v hs ht hinj hadj =>
    subst s
    subst t
    obtain ⟨q, hq⟩ := DirectedWalk.exists_of_sequence v hadj
    refine ⟨q, ?_⟩
    intro x hx
    exact (SimplePath.mem_vertices _ x).mpr (hq x hx)

/-- Concatenation followed by loop erasure preserves the demand endpoints. -/
theorem exists_composition (p : SimplePath G s u) (q : SimplePath G u t) :
    ∃ r : SimplePath G s t, r.vertices ⊆ p.vertices ∪ q.vertices := by
  obtain ⟨a, ha⟩ := p.exists_directedWalk
  obtain ⟨b, hb⟩ := q.exists_directedWalk
  obtain ⟨r, hr⟩ := (a.append b).exists_simplePath
  refine ⟨r, hr.trans ?_⟩
  rw [DirectedWalk.append_vertices]
  exact Finset.union_subset_union ha hb

/-- The only additional possible interior vertex is the common endpoint. -/
theorem internalVertices_subset_of_composition (p : SimplePath G s u)
    (q : SimplePath G u t) (r : SimplePath G s t)
    (h : r.vertices ⊆ p.vertices ∪ q.vertices) :
    r.internalVertices ⊆ insert u (p.internalVertices ∪ q.internalVertices) := by
  intro v hv
  obtain ⟨hvr, hvs, hvt⟩ := (r.mem_internalVertices v).mp hv
  by_cases hvu : v = u
  · simp [hvu]
  · apply Finset.mem_insert_of_mem
    have hx := h ((r.mem_vertices v).mpr hvr)
    rcases Finset.mem_union.mp hx with hp | hq
    · exact Finset.mem_union_left _ ((p.mem_internalVertices v).mpr
        ⟨(p.mem_vertices v).mp hp, hvs, hvu⟩)
    · exact Finset.mem_union_right _ ((q.mem_internalVertices v).mpr
        ⟨(q.mem_vertices v).mp hq, hvu, hvt⟩)

/-- Nonnegative weights bound the cost of an extracted concatenation. -/
theorem weight_le_of_composition (p : SimplePath G s u) (q : SimplePath G u t)
    (r : SimplePath G s t) (h : r.vertices ⊆ p.vertices ∪ q.vertices)
    (w : V → ℝ≥0) : r.weight w ≤ p.weight w + q.weight w + w u := by
  have hsum : (∑ v ∈ p.internalVertices ∪ q.internalVertices, w v) ≤
      p.weight w + q.weight w := by
    calc
      _ ≤ (∑ v ∈ p.internalVertices ∪ q.internalVertices, w v) +
          ∑ v ∈ p.internalVertices ∩ q.internalVertices, w v :=
        le_add_of_nonneg_right bot_le
      _ = _ := Finset.sum_union_inter
  calc
    r.weight w ≤ ∑ v ∈ insert u (p.internalVertices ∪ q.internalVertices), w v :=
      Finset.sum_le_sum_of_subset (p.internalVertices_subset_of_composition q r h)
    _ = w u + ∑ v ∈ p.internalVertices ∪ q.internalVertices, w v :=
      Finset.sum_insert (by simp)
    _ ≤ w u + (p.weight w + q.weight w) := add_le_add (le_refl _) hsum
    _ = p.weight w + q.weight w + w u := by ac_rfl

/-- A pair of directed simple paths yields a simple path of bounded cost. -/
theorem exists_composition_weight_le (p : SimplePath G s u) (q : SimplePath G u t)
    (w : V → ℝ≥0) : ∃ r : SimplePath G s t,
      r.vertices ⊆ p.vertices ∪ q.vertices ∧
      r.weight w ≤ p.weight w + q.weight w + w u := by
  obtain ⟨r, hr⟩ := p.exists_composition q
  exact ⟨r, hr, p.weight_le_of_composition q r hr w⟩

end SimplePath

/-- Reachability by a finite directed walk agrees with simple-path reachability. -/
theorem nonempty_simplePath_iff_directedWalk {G : Digraph V} {s t : V} :
    Nonempty (SimplePath G s t) ↔ Nonempty (DirectedWalk G s t) := by
  constructor
  · rintro ⟨p⟩
    obtain ⟨q, _hq⟩ := p.exists_directedWalk
    exact ⟨q⟩
  · rintro ⟨q⟩
    obtain ⟨p, _hp⟩ := q.exists_simplePath
    exact ⟨p⟩

/-- Infinite distance means there is no actual finite directed walk. -/
theorem vertexDistance_eq_top_iff_no_walk (G : Digraph V) (w : V → ℝ≥0) (s t : V) :
    vertexDistance G w s t = ⊤ ↔ ¬Nonempty (DirectedWalk G s t) := by
  rw [vertexDistance_eq_top_iff, nonempty_simplePath_iff_directedWalk]

/-- In a finite graph every reachable pair has a minimum-weight simple path. -/
theorem exists_minimumWeight_path [Fintype V] {G : Digraph V} (w : V → ℝ≥0)
    {s t : V} (h : Nonempty (SimplePath G s t)) :
    ∃ p : SimplePath G s t, ∀ q : SimplePath G s t, p.weight w ≤ q.weight w := by
  obtain ⟨p, _hp, hmin⟩ := Set.exists_min_image
    (Set.univ : Set (SimplePath G s t)) (fun p => p.weight w)
    (Set.toFinite _) (by rcases h with ⟨p⟩; exact ⟨p, Set.mem_univ p⟩)
  exact ⟨p, fun q => hmin q (Set.mem_univ q)⟩

/-- The extended infimum is attained whenever a path exists. -/
theorem vertexDistance_attained [Fintype V] {G : Digraph V} (w : V → ℝ≥0)
    {s t : V} (h : Nonempty (SimplePath G s t)) :
    ∃ p : SimplePath G s t, vertexDistance G w s t = (p.weight w : ℝ≥0∞) := by
  obtain ⟨p, hp⟩ := exists_minimumWeight_path w h
  refine ⟨p, le_antisymm (vertexDistance_le_weight w p) ?_⟩
  exact (coe_le_vertexDistance_iff G w s t (p.weight w)).mpr hp

/-- The endpoint-excluding distance triangle inequality charges the middle vertex.
Disconnected legs give an infinite right-hand side. No positivity assumption is
needed, and repeated demand endpoints and length-zero paths are included. -/
theorem vertexDistance_triangle [Fintype V] (G : Digraph V) (w : V → ℝ≥0)
    (s u t : V) : vertexDistance G w s t ≤
      vertexDistance G w s u + vertexDistance G w u t + (w u : ℝ≥0∞) := by
  by_cases hs : Nonempty (SimplePath G s u)
  · by_cases ht : Nonempty (SimplePath G u t)
    · obtain ⟨p, hp⟩ := vertexDistance_attained w hs
      obtain ⟨q, hq⟩ := vertexDistance_attained w ht
      obtain ⟨r, _hr, hw⟩ := p.exists_composition_weight_le q w
      calc
        vertexDistance G w s t ≤ (r.weight w : ℝ≥0∞) := vertexDistance_le_weight w r
        _ ≤ ((p.weight w + q.weight w + w u : ℝ≥0) : ℝ≥0∞) :=
          ENNReal.coe_le_coe.mpr hw
        _ = _ := by rw [hp, hq]; simp
    · rw [(vertexDistance_eq_top_iff G w u t).mpr ht]
      simp
  · rw [(vertexDistance_eq_top_iff G w s u).mpr hs]
    simp

end

end DirectedFlowCutGap
