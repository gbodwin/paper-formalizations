import OnlineReachabilityPreservers.Restricted

/-! Lemma 10 for the forward compressed path system and its reversed counterpart. -/

namespace OnlineReachabilityPreservers

open Finset Relation

/-- A bridge with `k + 2` vertices. The arcs and the river are all distinct paths. -/
structure Bridge {V I : Type*} (before : I → V → V → Prop) (k : ℕ) where
  vertex : Fin (k + 2) → V
  arc : Fin (k + 1) → I
  river : I
  distinctVertices : Function.Injective vertex
  distinctArcs : Function.Injective arc
  river_ne_arc : ∀ i, river ≠ arc i
  riverStep : before river (vertex 0) (vertex (Fin.last (k + 1)))
  arcStep : ∀ i, before (arc i) (vertex i.castSucc) (vertex i.succ)

variable {V : Type*} [LinearOrder V] [Fintype V]

/-- The forward compression keeps new-edge tails and the terminal.
An ignored unreachable request can be recorded as a singleton terminal. -/
def compressed (G : Arcs V) (D : List (V × V)) (i : Fin D.length) : Finset V :=
  insert (D.get i).2 (marks G D i)

/-- On a DAG walk the order on its vertices is the restriction of strict reachability. -/
def CompressedBefore (G : Arcs V) (D : List (V × V)) (i : Fin D.length) (u v : V) : Prop :=
  u ∈ compressed G D i ∧ v ∈ compressed G D i ∧ u ≠ v ∧ Reach G u v

omit [LinearOrder V] [Fintype V] in
theorem dag_reach_antisymm {G : Arcs V} (dag : IsDAG G) {u v : V}
    (h : Reach G u v) (back : Reach G v u) : u = v := by
  rcases h.cases_head with eq | ⟨_, edge, rest⟩
  · exact eq
  · exact (dag edge (rest.trans back)).elim

theorem compressedBefore_topological {G : Arcs V} (dag : IsDAG G)
    {D : List (V × V)} {i : Fin D.length} {u v : V} (h : CompressedBefore G D i u v) :
    (reaches G u).card < (reaches G v).card := by
  rcases h.2.2.2.cases_head with eq | ⟨w, edge, rest⟩
  · exact (h.2.2.1 eq).elim
  · apply (reaches_card_lt dag edge).trans_le
    apply card_le_card
    intro x hx
    exact mem_reaches.mpr ((mem_reaches.mp hx).trans rest)

private theorem compressed_to_target {G : Arcs V} {D : List (V × V)} {i : Fin D.length}
    {u : V} (hu : u ∈ compressed G D i) : Reach G u (D.get i).2 := by
  rcases mem_insert.mp hu with eq | hm
  · exact eq ▸ ReflTransGen.refl
  · obtain ⟨e, he, rfl⟩ := mem_image.mp hm
    have edge : Edge G e.1 e.2 :=
      forwardEdges_subset (before_subset G D i) _ (mem_sdiff.mp he).1
    exact (new_edge_reaches_target he).head edge

theorem compressedBefore_total {G : Arcs V} {D : List (V × V)} {i : Fin D.length}
    {u v : V} (hu : u ∈ compressed G D i) (hv : v ∈ compressed G D i) (ne : u ≠ v) :
    CompressedBefore G D i u v ∨ CompressedBefore G D i v u := by
  by_cases hat : u = (D.get i).2
  · exact Or.inr ⟨hv, hu, ne.symm, hat.symm ▸ compressed_to_target hv⟩
  by_cases hbt : v = (D.get i).2
  · exact Or.inl ⟨hu, hv, ne, hbt.symm ▸ compressed_to_target hu⟩
  obtain ⟨a, ha, rfl⟩ := mem_image.mp ((mem_insert.mp hu).resolve_left hat)
  obtain ⟨b, hb, rfl⟩ := mem_image.mp ((mem_insert.mp hv).resolve_left hbt)
  have sub := before_subset G D i
  have ha' := (mem_sdiff.mp ha).1
  have hb' := (mem_sdiff.mp hb).1
  have hab : a ≠ b := fun h => ne (congrArg Prod.fst h)
  rcases forward_edge_order sub ha' hb' hab with h | h
  · exact Or.inl ⟨hu, hv, ne, h.head (forwardEdges_subset sub _ ha')⟩
  · exact Or.inr ⟨hv, hu, ne.symm, h.head (forwardEdges_subset sub _ hb')⟩

private theorem target_not_mark {G : Arcs V} (dag : IsDAG G) (D : List (V × V))
    (i : Fin D.length) : (D.get i).2 ∉ marks G D i := by
  intro h
  obtain ⟨e, he, heq⟩ := mem_image.mp h
  have edge : Edge G e.1 e.2 :=
    forwardEdges_subset (before_subset G D i) _ (mem_sdiff.mp he).1
  exact dag edge (heq.symm ▸ new_edge_reaches_target he)

/-- Each chosen path contributes one terminal in addition to its new-edge tails. -/
theorem compressed_total {G : Arcs V} (dag : IsDAG G) (D : List (V × V)) :
    (∑ i : Fin D.length, (compressed G D i).card) = (forwardRun G D).card + D.length := by
  have h (i : Fin D.length) : (compressed G D i).card = (marks G D i).card + 1 :=
    card_insert_of_notMem (target_not_mark dag D i)
  simp only [h, sum_add_distrib, sum_marks_card dag, sum_const, card_univ, Fintype.card_fin,
    smul_eq_mul, mul_one]

private theorem compressed_exit {G : Arcs V} (dag : IsDAG G) {D : List (V × V)}
    {i : Fin D.length} {u v : V} (h : CompressedBefore G D i u v) :
    ∃ e ∈ newEdges G D i, e.1 = u ∧ Reach G e.2 v := by
  obtain ⟨hu, hv, ne, huv⟩ := h
  have hut : u ≠ (D.get i).2 := by
    intro eq
    exact ne (dag_reach_antisymm dag huv (eq.symm ▸ compressed_to_target hv))
  obtain ⟨e, he, rfl⟩ := mem_image.mp ((mem_insert.mp hu).resolve_left hut)
  refine ⟨e, he, rfl, ?_⟩
  rcases mem_insert.mp hv with eq | mark
  · exact eq ▸ new_edge_reaches_target he
  · obtain ⟨f, hf, rfl⟩ := mem_image.mp mark
    have hne : e ≠ f := fun eq => ne (congrArg Prod.fst eq)
    rcases forward_edge_order (before_subset G D i) (mem_sdiff.mp he).1
        (mem_sdiff.mp hf).1 hne with hr | hr
    · exact hr
    · have edge : Edge G f.1 f.2 :=
        forwardEdges_subset (before_subset G D i) _ (mem_sdiff.mp hf).1
      exact (ne (dag_reach_antisymm dag huv (hr.head edge))).elim

/-- Under forward growth, the first arc of a bridge cannot precede its river. -/
theorem no_earlier_first_arc {G : Arcs V} (dag : IsDAG G) {D : List (V × V)} {k : ℕ}
    (b : Bridge (CompressedBefore G D) k) : ¬ b.arc 0 < b.river := by
  intro earlier
  obtain ⟨e, he, hex, next⟩ := compressed_exit dag (b.arcStep 0)
  obtain ⟨f, hf, hfx, _⟩ := compressed_exit dag b.riverStep
  have chain (i : Fin (k + 1)) : Reach G (b.vertex (0 : Fin (k + 1)).succ)
      (b.vertex i.succ) := by
    induction i using Fin.induction with
    | zero => exact .refl
    | succ j ih => exact ih.trans (b.arcStep j.succ).2.2.2
  have last : Reach G (b.vertex (Fin.last (k + 1))) (D.get b.river).2 :=
    compressed_to_target b.riverStep.2.1
  exact earlier_edge_conflict earlier he hf (hex.trans hfx.symm)
    ((next.trans (chain (Fin.last k))).trans last)

/-- The order on the backward system is the reverse of the order on its
forward system in the reversed graph. -/
def BackwardCompressedBefore (G : Arcs V) (D : List (V × V))
    (i : Fin (D.map Prod.swap).length) (u v : V) : Prop :=
  CompressedBefore (reverseArcs G) (D.map Prod.swap) i v u

theorem backwardCompressed_total {G : Arcs V} (dag : IsDAG G) (D : List (V × V)) :
    (∑ i : Fin (D.map Prod.swap).length,
      (compressed (reverseArcs G) (D.map Prod.swap) i).card) = (backwardRun G D).card + D.length := by
  simpa [backwardRun] using compressed_total (reverseArcs_dag dag) (D.map Prod.swap)

/-- Under backward growth, the last arc of a bridge cannot precede its river. -/
theorem no_earlier_last_arc {G : Arcs V} (dag : IsDAG G) {D : List (V × V)} {k : ℕ}
    (b : Bridge (BackwardCompressedBefore G D) k) : ¬ b.arc (Fin.last k) < b.river := by
  let rev : Bridge (CompressedBefore (reverseArcs G) (D.map Prod.swap)) k := {
    vertex := b.vertex ∘ Fin.rev
    arc := b.arc ∘ Fin.rev
    river := b.river
    distinctVertices := b.distinctVertices.comp Fin.rev_injective
    distinctArcs := b.distinctArcs.comp Fin.rev_injective
    river_ne_arc := fun i => b.river_ne_arc i.rev
    riverStep := by
      simpa [BackwardCompressedBefore, Function.comp_def, Fin.rev_zero, Fin.rev_last] using b.riverStep
    arcStep := by
      intro i
      have hr := b.arcStep i.rev
      change CompressedBefore (reverseArcs G) (D.map Prod.swap) (b.arc i.rev)
        (b.vertex (i.rev.succ)) (b.vertex (i.rev.castSucc)) at hr
      simpa [Function.comp_def, Fin.rev_castSucc, Fin.rev_succ] using hr }
  simpa [rev, Function.comp_def, Fin.rev_zero] using no_earlier_first_arc (reverseArcs_dag dag) rev

end OnlineReachabilityPreservers
