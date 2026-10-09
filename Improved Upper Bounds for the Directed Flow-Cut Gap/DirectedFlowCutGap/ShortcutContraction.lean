import DirectedFlowCutGap.TerminalPorts

/-!
# Shortcut contraction with permanent terminals

A shortcut has a positive-length directed simple-path witness whose internal
vertices belong to the removed finite set. Thus the shortcut graph is loopless;
original loops and closed excursions do not create spurious positive simple
paths. Concrete walk compression and expansion, followed by proved loop erasure,
give cut transfer and the exact finite removed-mass error in path weights.

The general statements require surviving demand endpoints. The final port
corollaries remove only cores, so every original demand retains its permanent
source/sink representatives. These are components of a repaired contraction step
in Theorem 29 of arXiv:2604.03412v3, not the complete unit-cost reduction.
-/

namespace DirectedFlowCutGap

noncomputable section

open scoped BigOperators NNReal ENNReal

namespace ShortcutContraction

variable {V : Type*} [DecidableEq V]

/-- The actual vertex type after removing `S`. -/
abbrev Survivor (S : Finset V) := {v : V // v ∉ S}

/-- Edges are witnessed by positive simple paths with only removed interiors. -/
def graph (G : Digraph V) (S : Finset V) : Digraph (Survivor S) where
  Adj u v := ∃ p : SimplePath G u.val v.val,
    0 < p.edgeLength ∧ p.internalVertices ⊆ S

omit [DecidableEq V] in
private theorem positive_of_ne {G : Digraph V} {s t : V}
    (p : SimplePath G s t) (h : s ≠ t) : 0 < p.edgeLength := by
  by_contra hn
  have hz : p.edgeLength = 0 := by omega
  have hi : (0 : Fin (p.edgeLength + 1)) = Fin.last p.edgeLength :=
    Fin.ext (by simp [hz])
  exact h (p.source_eq.symm.trans ((congrArg p.vertex hi).trans p.target_eq))

/-- Positive simple paths cannot close up; self-loops are deliberately absent. -/
theorem not_adj_self (G : Digraph V) (S : Finset V) (u : Survivor S) :
    ¬(graph G S).Adj u u := by
  rintro ⟨p, hp, _⟩
  have hi := p.injective (p.source_eq.trans p.target_eq.symm)
  have hv := congrArg Fin.val hi
  simp only [Fin.val_zero, Fin.val_last] at hv
  omega

private theorem path_support {G : Digraph V} {s t : V}
    (p : SimplePath G s t) (S : Finset V) (h : p.internalVertices ⊆ S) :
    p.vertices ⊆ insert s (insert t S) := by
  intro x hx
  by_cases hs : x = s
  · simp [hs]
  by_cases ht : x = t
  · simp [ht]
  exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
    (h ((p.mem_internalVertices x).mpr ⟨(p.mem_vertices x).mp hx, hs, ht⟩)))

/-- Expanding every shortcut edge gives a genuine original walk. -/
theorem expand_walk {G : Digraph V} {S : Finset V} {s t : Survivor S}
    (q : DirectedWalk (graph G S) s t) :
    ∃ p : DirectedWalk G s.val t.val,
      p.vertices ⊆ q.vertices.image Subtype.val ∪ S := by
  induction q with
  | refl s =>
    refine ⟨.refl s.val, ?_⟩
    simp [DirectedWalk.vertices]
  | @cons s u t h q ih =>
    obtain ⟨a, _ha, hai⟩ := h
    obtain ⟨b, hb⟩ := a.exists_directedWalk
    obtain ⟨c, hc⟩ := ih
    refine ⟨b.append c, ?_⟩
    rw [DirectedWalk.append_vertices]
    apply Finset.union_subset
    · intro x hx
      have hx' := path_support a S hai (hb hx)
      simp only [Finset.mem_insert] at hx'
      rcases hx' with rfl | rfl | hx'
      · simp [DirectedWalk.vertices]
      · apply Finset.mem_union_left
        apply Finset.mem_image.mpr
        exact ⟨u, Finset.mem_insert_of_mem q.source_mem_vertices, rfl⟩
      · exact Finset.mem_union_right _ hx'
    · exact hc.trans (Finset.union_subset_union
        (Finset.image_subset_image (Finset.subset_insert _ _)) (Finset.Subset.refl _))

/-- The expansion retains only shortcut interiors and removed vertices internally. -/
theorem expand_path {G : Digraph V} {S : Finset V} {s t : Survivor S}
    (q : SimplePath (graph G S) s t) :
    ∃ p : SimplePath G s.val t.val,
      p.internalVertices ⊆ q.internalVertices.image Subtype.val ∪ S := by
  obtain ⟨a, ha⟩ := q.exists_directedWalk
  obtain ⟨b, hb⟩ := expand_walk a
  obtain ⟨p, hp⟩ := b.exists_simplePath
  refine ⟨p, ?_⟩
  intro x hx
  obtain ⟨hxp, hxs, hxt⟩ := (p.mem_internalVertices x).mp hx
  have hxm := hb (hp ((p.mem_vertices x).mpr hxp))
  rcases Finset.mem_union.mp hxm with hxm | hxm
  · obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hxm
    apply Finset.mem_union_left
    apply Finset.mem_image.mpr
    refine ⟨u, (q.mem_internalVertices u).mpr ?_, rfl⟩
    exact ⟨(q.mem_vertices u).mp (ha hu), fun he => hxs (congrArg Subtype.val he),
      fun he => hxt (congrArg Subtype.val he)⟩
  · exact Finset.mem_union_right _ hxm

/-- The prefix before the first surviving vertex can be kept as an actual walk.
The remainder is already a shortcut walk, with retained support. -/
private theorem compress_prefix {G : Digraph V} (S : Finset V) {s t : V}
    (p : DirectedWalk G s t) (ht : t ∉ S) :
    ∃ u : Survivor S, ∃ a : DirectedWalk G s u.val,
      ∃ b : DirectedWalk (graph G S) u ⟨t, ht⟩,
        a.vertices ⊆ p.vertices ∧ a.vertices ⊆ insert u.val S ∧
        b.vertices.image Subtype.val ⊆ p.vertices ∧ (s ∉ S → u.val = s) := by
  induction p with
  | refl t =>
    refine ⟨⟨t, ht⟩, .refl t, DirectedWalk.refl (G := graph G S) ⟨t, ht⟩, ?_, ?_, ?_, ?_⟩
    · exact Finset.Subset.refl _
    · simp [DirectedWalk.vertices]
    · simp [DirectedWalk.vertices]
    · intro _; rfl
  | @cons s v t edge p ih =>
    obtain ⟨u, a, b, ha, hai, hb, _hfirst⟩ := ih ht
    by_cases hs : s ∈ S
    · refine ⟨u, .cons edge a, b, ?_, ?_, ?_, ?_⟩
      · exact Finset.insert_subset_insert _ ha
      · exact Finset.insert_subset (Finset.mem_insert_of_mem hs) hai
      · exact hb.trans (Finset.subset_insert _ _)
      · intro h; exact (h hs).elim
    · let s' : Survivor S := ⟨s, hs⟩
      have hwalk : ∃ c : DirectedWalk (graph G S) s' ⟨t, ht⟩,
          c.vertices.image Subtype.val ⊆ insert s p.vertices := by
        by_cases he : s' = u
        · subst u
          exact ⟨b, hb.trans (Finset.subset_insert _ _)⟩
        · obtain ⟨c, hc⟩ := (DirectedWalk.cons edge a).exists_simplePath
          have hpos : 0 < c.edgeLength := positive_of_ne c
            (fun hsu => he (Subtype.ext hsu))
          have hci : c.internalVertices ⊆ S := by
            intro x hx
            obtain ⟨hxc, hxs, hxu⟩ := (c.mem_internalVertices x).mp hx
            have hx' := hc ((c.mem_vertices x).mpr hxc)
            simp only [DirectedWalk.vertices, Finset.mem_insert] at hx'
            rcases hx' with hxs' | hxa
            · exact (hxs hxs').elim
            · have hx'' := hai hxa
              simp only [Finset.mem_insert] at hx''
              exact hx''.resolve_left hxu
          refine ⟨.cons ⟨c, hpos, hci⟩ b, ?_⟩
          simpa only [DirectedWalk.vertices, Finset.image_insert] using
            Finset.insert_subset_insert s hb
      obtain ⟨c, hc⟩ := hwalk
      refine ⟨s', .refl s, c, ?_, ?_, hc, ?_⟩
      · simp [DirectedWalk.vertices]
      · simp [DirectedWalk.vertices, s']
      · intro _; rfl

/-- Compression of an original walk with surviving endpoints is constructive
at the level of graph paths: its retained vertices come from the original walk. -/
theorem compress_walk {G : Digraph V} {S : Finset V} {s t : Survivor S}
    (p : DirectedWalk G s.val t.val) :
    ∃ q : DirectedWalk (graph G S) s t,
      q.vertices.image Subtype.val ⊆ p.vertices := by
  obtain ⟨u, _a, b, _ha, _hai, hb, hfirst⟩ := compress_prefix S p t.property
  have hu : u = s := Subtype.ext (hfirst s.property)
  subst u
  exact ⟨b, hb⟩

/-- Every original simple path between survivors compresses to an actual
shortcut simple path with no new surviving internal vertices. -/
theorem compress_path {G : Digraph V} {S : Finset V} {s t : Survivor S}
    (p : SimplePath G s.val t.val) :
    ∃ q : SimplePath (graph G S) s t,
      q.internalVertices.image Subtype.val ⊆ p.internalVertices := by
  obtain ⟨a, ha⟩ := p.exists_directedWalk
  obtain ⟨b, hb⟩ := compress_walk a
  obtain ⟨q, hq⟩ := b.exists_simplePath
  refine ⟨q, ?_⟩
  intro x hx
  obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hx
  obtain ⟨huq, hus, hut⟩ := (q.mem_internalVertices u).mp hu
  apply (p.mem_internalVertices u.val).mpr
  refine ⟨(p.mem_vertices u.val).mp ?_, ?_, ?_⟩
  · exact ha (hb (Finset.mem_image.mpr
      ⟨u, hq ((q.mem_vertices u).mpr huq), rfl⟩))
  · intro he; exact hus (Subtype.ext he)
  · intro he; exact hut (Subtype.ext he)

/-- Restricted weights sum exactly over the injective surviving-vertex map. -/
theorem sum_image_val (w : V → ℝ≥0) {S : Finset V} (X : Finset (Survivor S)) :
    ∑ x ∈ X.image Subtype.val, w x = ∑ x ∈ X, w x.val := by
  rw [Finset.sum_image]
  intro a _ b _ h
  exact Subtype.ext h

/-- The contraction error is the total mass of the finite removed set, once,
regardless of how often expanded shortcut witnesses revisit removed vertices. -/
theorem expand_path_weight_le {G : Digraph V} {S : Finset V} {s t : Survivor S}
    (q : SimplePath (graph G S) s t) (w : V → ℝ≥0) :
    ∃ p : SimplePath G s.val t.val,
      p.internalVertices ⊆ q.internalVertices.image Subtype.val ∪ S ∧
      p.weight w ≤ q.weight (fun v => w v.val) + ∑ v ∈ S, w v := by
  obtain ⟨p, hp⟩ := expand_path q
  refine ⟨p, hp, ?_⟩
  have hd : Disjoint (q.internalVertices.image Subtype.val) S := by
    apply Finset.disjoint_left.mpr
    intro v hv hs
    obtain ⟨u, _hu, rfl⟩ := Finset.mem_image.mp hv
    exact u.property hs
  calc
    p.weight w ≤ ∑ v ∈ q.internalVertices.image Subtype.val ∪ S, w v :=
      Finset.sum_le_sum_of_subset hp
    _ = q.weight (fun v => w v.val) + ∑ v ∈ S, w v := by
      rw [Finset.sum_union hd, sum_image_val]
      rfl

/-- Integral cuts pull back along surviving vertices without selecting `S`. -/
theorem cutsPair_pullback {G : Digraph V} {S : Finset V} {s t : Survivor S}
    (Y : Finset (Survivor S)) (h : CutsPair (graph G S) Y s t) :
    CutsPair G (Y.image Subtype.val) s.val t.val := by
  intro p
  obtain ⟨q, hq⟩ := compress_path p
  obtain ⟨v, hv, hvY⟩ := h q
  exact ⟨v.val, hq (Finset.mem_image.mpr ⟨v, hv, rfl⟩),
    Finset.mem_image.mpr ⟨v, hvY, rfl⟩⟩

/-- Conversely, an original cut disjoint from removed vertices cuts shortcuts. -/
theorem cutsPair_iff {G : Digraph V} {S : Finset V} {s t : Survivor S}
    (Y : Finset (Survivor S)) :
    CutsPair (graph G S) Y s t ↔ CutsPair G (Y.image Subtype.val) s.val t.val := by
  constructor
  · exact cutsPair_pullback Y
  · intro h q
    obtain ⟨p, hp⟩ := expand_path q
    obtain ⟨v, hv, hvY⟩ := h p
    obtain ⟨u, huY, rfl⟩ := Finset.mem_image.mp hvY
    rcases Finset.mem_union.mp (hp hv) with huv | huS
    · obtain ⟨z, hz, hzu⟩ := Finset.mem_image.mp huv
      have : z = u := Subtype.ext hzu
      subst z
      exact ⟨u, hz, huY⟩
    · exact (u.property huS).elim

/-- An original cut explicitly disjoint from `S` has exactly the same
feasibility after restriction to the surviving vertex type. -/
theorem cutsPair_disjoint_iff {G : Digraph V} {S : Finset V} {s t : Survivor S}
    (X : Finset V) (hXS : Disjoint X S) :
    CutsPair (graph G S) (X.subtype (fun v => v ∉ S)) s t ↔
      CutsPair G X s.val t.val := by
  have heq : (X.subtype (fun v => v ∉ S)).image Subtype.val = X := by
    ext v
    constructor
    · intro hv
      obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hv
      exact Finset.mem_subtype.mp hu
    · intro hv
      have hs : v ∉ S := fun hs => Finset.disjoint_left.mp hXS hv hs
      exact Finset.mem_image.mpr ⟨⟨v, hs⟩, Finset.mem_subtype.mpr hv, rfl⟩
  rw [cutsPair_iff, heq]

/-- Pulling back a surviving cut preserves its cost exactly. -/
theorem cutCost_pullback (cost : V → ℝ≥0) {S : Finset V}
    (Y : Finset (Survivor S)) :
    cutCost cost (Y.image Subtype.val) = cutCost (fun v => cost v.val) Y :=
  sum_image_val cost Y

/-- Only demands whose two endpoints actually survive are represented here. -/
def survivingDemands (S : Finset V) (D : Set (V × V)) :
    Set (Survivor S × Survivor S) := {st | (st.1.val, st.2.val) ∈ D}

/-- A cut of the shortcut demand family pulls back for every original demand
provided both original endpoints are explicitly known to survive. -/
theorem isIntegralCut_pullback {G : Digraph V} {S : Finset V} {D : Set (V × V)}
    (hends : ∀ s t, (s, t) ∈ D → s ∉ S ∧ t ∉ S)
    (Y : Finset (Survivor S))
    (h : IsIntegralCut (graph G S) Y (survivingDemands S D)) :
    IsIntegralCut G (Y.image Subtype.val) D := by
  intro s t hst
  obtain ⟨hs, ht⟩ := hends s t hst
  exact cutsPair_pullback (s := ⟨s, hs⟩) (t := ⟨t, ht⟩) Y
    (h ⟨s, hs⟩ ⟨t, ht⟩ hst)

/-- A finite removed mass at most one half preserves distance at least one half.
There is no hidden positive-weight or finite-distance assumption. -/
theorem half_le_vertexDistance {G : Digraph V} {S : Finset V} {s t : Survivor S}
    (w : V → ℝ≥0) (hmass : (∑ v ∈ S, w v) ≤ (1 / 2 : ℝ≥0))
    (h : 1 ≤ vertexDistance G w s.val t.val) :
    (1 / 2 : ℝ≥0∞) ≤ vertexDistance (graph G S) (fun v => w v.val) s t := by
  have hh : ((1 / 2 : ℝ≥0) : ℝ≥0∞) = (1 / 2 : ℝ≥0∞) := by norm_num
  rw [← hh, coe_le_vertexDistance_iff]
  intro q
  obtain ⟨p, _hp, hw⟩ := expand_path_weight_le q w
  have horig : (1 : ℝ≥0) ≤ p.weight w :=
    (coe_le_vertexDistance_iff G w s.val t.val 1).mp (by simpa using h) p
  linarith

/-- Doubling remaining weights restores the unit fractional threshold. -/
theorem one_le_vertexDistance_double {G : Digraph V} {S : Finset V}
    {s t : Survivor S} (w : V → ℝ≥0)
    (hmass : (∑ v ∈ S, w v) ≤ (1 / 2 : ℝ≥0))
    (h : 1 ≤ vertexDistance G w s.val t.val) :
    1 ≤ vertexDistance (graph G S) (fun v => 2 * w v.val) s t := by
  rw [← ENNReal.coe_one, coe_le_vertexDistance_iff]
  intro q
  obtain ⟨p, _hp, hw⟩ := expand_path_weight_le q w
  have horig : (1 : ℝ≥0) ≤ p.weight w :=
    (coe_le_vertexDistance_iff G w s.val t.val 1).mp (by simpa using h) p
  have heq : q.weight (fun v => 2 * w v.val) = 2 * q.weight (fun v => w v.val) := by
    simp only [SimplePath.weight, Finset.mul_sum]
  rw [heq]
  linarith

/-- Fractional feasibility for surviving demands under the exact mass bound. -/
theorem isFractionalCut_double {G : Digraph V} {S : Finset V} {D : Set (V × V)}
    (w : V → ℝ≥0) (hmass : (∑ v ∈ S, w v) ≤ (1 / 2 : ℝ≥0))
    (h : IsFractionalCut G w D) :
    IsFractionalCut (graph G S) (fun v => 2 * w v.val) (survivingDemands S D) := by
  intro s t hst
  exact one_le_vertexDistance_double w hmass (h s.val t.val hst)

omit [DecidableEq V] in
/-- Uniform small weights imply the cardinality-times-threshold mass bound. -/
theorem removed_mass_le (S : Finset V) (w : V → ℝ≥0) (a : ℝ≥0)
    (h : ∀ v ∈ S, w v ≤ a) : (∑ v ∈ S, w v) ≤ S.card * a := by
  calc
    _ ≤ ∑ _v ∈ S, a := Finset.sum_le_sum h
    _ = _ := by simp [nsmul_eq_mul]

omit [DecidableEq V] in
/-- The usual `1/(2n)` cutoff supplies the exact `|S|/(2n)` error. -/
theorem removed_mass_le_card_div (S : Finset V) (w : V → ℝ≥0) (n : ℕ)
    (h : ∀ v ∈ S, w v ≤ 1 / (2 * n : ℝ≥0)) :
    (∑ v ∈ S, w v) ≤ (S.card : ℝ≥0) / (2 * n) := by
  simpa only [mul_one_div] using removed_mass_le S w _ h

omit [DecidableEq V] in
/-- In a finite graph the standard small-vertex cutoff removes at most half. -/
theorem removed_mass_le_half [Fintype V] (S : Finset V) (w : V → ℝ≥0)
    (h : ∀ v ∈ S, w v ≤ 1 / (2 * Fintype.card V : ℝ≥0)) :
    (∑ v ∈ S, w v) ≤ (1 / 2 : ℝ≥0) := by
  have hc : (S.card : ℝ≥0) ≤ Fintype.card V := by exact_mod_cast Finset.card_le_univ S
  have hm := removed_mass_le_card_div S w (Fintype.card V) h
  by_cases hn : Fintype.card V = 0
  · have hS : S = ∅ := Finset.card_eq_zero.mp (by have := Finset.card_le_univ S; omega)
    simp [hS]
  · have hn' : (0 : ℝ≥0) < Fintype.card V := by exact_mod_cast Nat.pos_of_ne_zero hn
    calc
      _ ≤ (S.card : ℝ≥0) / (2 * Fintype.card V) := hm
      _ ≤ (Fintype.card V : ℝ≥0) / (2 * Fintype.card V) := div_le_div_of_nonneg_right hc bot_le
      _ = 1 / 2 := by field_simp

/-- Removed cores only: all terminal representatives remain present. -/
def portSource (S : Finset V) (s : V) : Survivor (S.image TerminalPorts.core) :=
  ⟨TerminalPorts.source s, by simp⟩

def portSink (S : Finset V) (t : V) : Survivor (S.image TerminalPorts.core) :=
  ⟨TerminalPorts.sink t, by simp⟩

/-- Every original demand is represented, even when its cores are removed. -/
def portDemands (S : Finset V) (D : Set (V × V)) :
    Set (Survivor (S.image TerminalPorts.core) × Survivor (S.image TerminalPorts.core)) :=
  (fun st => (portSource S st.1, portSink S st.2)) '' D

/-- Permanent ports repair the endpoint loss in low-weight contraction. -/
theorem port_isFractionalCut_double {G : Digraph V} {S : Finset V}
    {D : Set (V × V)} (w : V → ℝ≥0)
    (hmass : (∑ v ∈ S, w v) ≤ (1 / 2 : ℝ≥0)) (h : IsFractionalCut G w D) :
    IsFractionalCut (graph (TerminalPorts.graph G) (S.image TerminalPorts.core))
      (fun v => 2 * TerminalPorts.extend w v.val) (portDemands S D) := by
  intro a b hab
  obtain ⟨⟨s, t⟩, hst, he⟩ := hab
  have ha : portSource S s = a := congrArg Prod.fst he
  have hb : portSink S t = b := congrArg Prod.snd he
  subst a
  subst b
  apply one_le_vertexDistance_double (TerminalPorts.extend w)
  · simpa only [TerminalPorts.sum_extend_image] using hmass
  · simpa only [portSource, portSink, TerminalPorts.vertexDistance_eq] using h s t hst

/-- Pull back a shortcut cut at permanent ports to an original core cut. -/
theorem port_isIntegralCut_pullback {G : Digraph V} {S : Finset V}
    {D : Set (V × V)} (Y : Finset (Survivor (S.image TerminalPorts.core)))
    (h : IsIntegralCut (graph (TerminalPorts.graph G) (S.image TerminalPorts.core))
      Y (portDemands S D)) :
    IsIntegralCut G (TerminalPorts.corePreimage (Y.image Subtype.val)) D := by
  intro s t hst
  apply (TerminalPorts.cutsPair_iff G (Y.image Subtype.val) s t).mp
  exact cutsPair_pullback Y (h (portSource S s) (portSink S t) ⟨(s, t), hst, rfl⟩)

/-- The final original cut has exactly the cost of the surviving port cut,
with zero cost on the permanent source and sink representatives. -/
theorem port_cutCost_pullback (cost : V → ℝ≥0) {S : Finset V}
    (Y : Finset (Survivor (S.image TerminalPorts.core))) :
    cutCost cost (TerminalPorts.corePreimage (Y.image Subtype.val)) =
      cutCost (fun v => TerminalPorts.extend cost v.val) Y := by
  rw [TerminalPorts.cutCost_corePreimage, cutCost_pullback]

end ShortcutContraction

end

end DirectedFlowCutGap
