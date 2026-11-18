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

/-- Reverse the chain and river while keeping the same path indices. -/
def Bridge.reverse {V I : Type*} {before : I → V → V → Prop} {k : ℕ}
    (b : Bridge before k) : Bridge (fun i u v => before i v u) k where
  vertex := b.vertex ∘ Fin.rev
  arc := b.arc ∘ Fin.rev
  river := b.river
  distinctVertices := b.distinctVertices.comp Fin.rev_injective
  distinctArcs := b.distinctArcs.comp Fin.rev_injective
  river_ne_arc := fun i => b.river_ne_arc i.rev
  riverStep := by
    simpa [Function.comp_def, Fin.rev_zero, Fin.rev_last] using b.riverStep
  arcStep := by
    intro i
    simpa [Function.comp_def, Fin.rev_castSucc, Fin.rev_succ] using b.arcStep i.rev

/-- Transport a bridge along an injective relabeling of its vertices. -/
def Bridge.mapVertices {V W I : Type*} {before : I → V → V → Prop}
    {after : I → W → W → Prop} {k : ℕ} (b : Bridge before k)
    (f : V → W) (hf : Function.Injective f) (h : ∀ i u v, before i u v → after i (f u) (f v)) :
    Bridge after k where
  vertex := f ∘ b.vertex
  arc := b.arc
  river := b.river
  distinctVertices := hf.comp b.distinctVertices
  distinctArcs := b.distinctArcs
  river_ne_arc := b.river_ne_arc
  riverStep := h _ _ _ b.riverStep
  arcStep i := h _ _ _ (b.arcStep i)

/-- Relabel the paths of a bridge while preserving their steps. -/
def Bridge.mapPaths {V I J : Type*} {before : I → V → V → Prop}
    {after : J → V → V → Prop} {k : ℕ} (b : Bridge before k)
    (f : I → J) (hf : Function.Injective f) (h : ∀ i u v, before i u v → after (f i) u v) :
    Bridge after k where
  vertex := b.vertex
  arc := f ∘ b.arc
  river := f b.river
  distinctVertices := b.distinctVertices
  distinctArcs := hf.comp b.distinctArcs
  river_ne_arc := fun i eq => b.river_ne_arc i (hf eq)
  riverStep := h _ _ _ b.riverStep
  arcStep i := h _ _ _ (b.arcStep i)

variable {V : Type*} [LinearOrder V] [Fintype V]

/-- The new-edge or critical-edge tails of a walk, together with its end. -/
def markedPath (A : Arcs V) (t : V) : Finset V := insert t (A.image Prod.fst)

/-- Strict reach order restricted to a set of vertices on a path. -/
def BeforeIn (G : Arcs V) (S : Finset V) (u v : V) : Prop :=
  u ∈ S ∧ v ∈ S ∧ u ≠ v ∧ Reach G u v

omit [LinearOrder V] [Fintype V] in
theorem dag_reach_antisymm {G : Arcs V} (dag : IsDAG G) {u v : V}
    (h : Reach G u v) (back : Reach G v u) : u = v := by
  rcases h.cases_head with eq | ⟨_, edge, rest⟩
  · exact eq
  · exact (dag edge (rest.trans back)).elim

theorem BeforeIn.rank_lt {G : Arcs V} (dag : IsDAG G) {S : Finset V}
    {u v : V} (h : BeforeIn G S u v) : (reaches G u).card < (reaches G v).card := by
  rcases h.2.2.2.cases_head with eq | ⟨w, edge, rest⟩
  · exact (h.2.2.1 eq).elim
  · apply (reaches_card_lt dag edge).trans_le
    apply card_le_card
    intro x hx
    exact mem_reaches.mpr ((mem_reaches.mp hx).trans rest)

theorem markedPath_to_target {G H A : Arcs V} {d : V × V}
    (sub : H ⊆ G) (chosen : A ⊆ forwardEdges G H d)
    {u : V} (hu : u ∈ markedPath A d.2) : Reach G u d.2 := by
  rcases mem_insert.mp hu with eq | hm
  · exact eq ▸ ReflTransGen.refl
  · obtain ⟨e, he, rfl⟩ := mem_image.mp hm
    exact (forward_edge_to_end sub (chosen he)).head (forwardEdges_subset sub _ (chosen he))

theorem markedPath_total {G H A : Arcs V} {d : V × V}
    (sub : H ⊆ G) (chosen : A ⊆ forwardEdges G H d)
    {u v : V} (hu : u ∈ markedPath A d.2) (hv : v ∈ markedPath A d.2) (ne : u ≠ v) :
    BeforeIn G (markedPath A d.2) u v ∨ BeforeIn G (markedPath A d.2) v u := by
  by_cases hut : u = d.2
  · exact Or.inr ⟨hv, hu, ne.symm, hut.symm ▸ markedPath_to_target sub chosen hv⟩
  by_cases hvt : v = d.2
  · exact Or.inl ⟨hu, hv, ne, hvt.symm ▸ markedPath_to_target sub chosen hu⟩
  obtain ⟨a, ha, rfl⟩ := mem_image.mp ((mem_insert.mp hu).resolve_left hut)
  obtain ⟨b, hb, rfl⟩ := mem_image.mp ((mem_insert.mp hv).resolve_left hvt)
  rcases forward_edge_order sub (chosen ha) (chosen hb) (fun h => ne (congrArg Prod.fst h)) with h | h
  · exact Or.inl ⟨hu, hv, ne, h.head (forwardEdges_subset sub _ (chosen ha))⟩
  · exact Or.inr ⟨hv, hu, ne.symm, h.head (forwardEdges_subset sub _ (chosen hb))⟩

theorem markedPath_card {G H A : Arcs V} {d : V × V} (dag : IsDAG G)
    (sub : H ⊆ G) (chosen : A ⊆ forwardEdges G H d) :
    (markedPath A d.2).card = A.card + 1 := by
  have target : d.2 ∉ A.image Prod.fst := by
    intro hw
    obtain ⟨e, he, eq⟩ := mem_image.mp hw
    exact dag (forwardEdges_subset sub _ (chosen he))
      (eq.symm ▸ forward_edge_to_end sub (chosen he))
  rw [markedPath, card_insert_of_notMem target]
  congr 1
  apply card_image_of_injOn
  intro e he f hf eq
  by_contra hne
  rcases forward_edge_order sub (chosen he) (chosen hf) hne with h | h
  · exact dag (forwardEdges_subset sub _ (chosen he)) (eq.symm ▸ h)
  · exact dag (forwardEdges_subset sub _ (chosen hf)) (eq ▸ h)

theorem markedPath_exit {G H A : Arcs V} {d : V × V} (dag : IsDAG G)
    (sub : H ⊆ G) (chosen : A ⊆ forwardEdges G H d)
    {u v : V} (h : BeforeIn G (markedPath A d.2) u v) :
    ∃ e ∈ A, e.1 = u ∧ Reach G e.2 v := by
  obtain ⟨hu, hv, ne, huv⟩ := h
  have hut : u ≠ d.2 := fun eq =>
    ne (dag_reach_antisymm dag huv (eq.symm ▸ markedPath_to_target sub chosen hv))
  obtain ⟨e, he, rfl⟩ := mem_image.mp ((mem_insert.mp hu).resolve_left hut)
  refine ⟨e, he, rfl, ?_⟩
  rcases mem_insert.mp hv with eq | hm
  · exact eq ▸ forward_edge_to_end sub (chosen he)
  · obtain ⟨f, hf, rfl⟩ := mem_image.mp hm
    rcases forward_edge_order sub (chosen he) (chosen hf) (fun eq => ne (congrArg Prod.fst eq)) with hr | hr
    · exact hr
    · exact (ne (dag_reach_antisymm dag huv (hr.head (forwardEdges_subset sub _ (chosen hf))))).elim

/-- The forward compression keeps new-edge tails and the terminal.
An ignored unreachable request can be recorded as a singleton terminal. -/
def compressed (G : Arcs V) (D : List (V × V)) (i : Fin D.length) : Finset V :=
  markedPath (newEdges G D i) (D.get i).2

/-- On a DAG walk the order on its vertices is the restriction of strict reachability. -/
def CompressedBefore (G : Arcs V) (D : List (V × V)) (i : Fin D.length) (u v : V) : Prop :=
  BeforeIn G (compressed G D i) u v

theorem compressedBefore_topological {G : Arcs V} (dag : IsDAG G)
    {D : List (V × V)} {i : Fin D.length} {u v : V} (h : CompressedBefore G D i u v) :
    (reaches G u).card < (reaches G v).card :=
  BeforeIn.rank_lt dag h

private theorem newEdges_on_path (G : Arcs V) (D : List (V × V)) (i : Fin D.length) :
    newEdges G D i ⊆ forwardEdges G (before G D i) (D.get i) :=
  fun _ h => (mem_sdiff.mp h).1

private theorem compressed_to_target {G : Arcs V} {D : List (V × V)} {i : Fin D.length}
    {u : V} (hu : u ∈ compressed G D i) : Reach G u (D.get i).2 :=
  markedPath_to_target (before_subset G D i) (newEdges_on_path G D i) hu

theorem compressedBefore_total {G : Arcs V} {D : List (V × V)} {i : Fin D.length}
    {u v : V} (hu : u ∈ compressed G D i) (hv : v ∈ compressed G D i) (ne : u ≠ v) :
    CompressedBefore G D i u v ∨ CompressedBefore G D i v u :=
  markedPath_total (before_subset G D i) (newEdges_on_path G D i) hu hv ne

/-- Each chosen path contributes one terminal in addition to its new-edge tails. -/
theorem compressed_total {G : Arcs V} (dag : IsDAG G) (D : List (V × V)) :
    (∑ i : Fin D.length, (compressed G D i).card) = (forwardRun G D).card + D.length := by
  have h (i : Fin D.length) : (compressed G D i).card = (newEdges G D i).card + 1 :=
    markedPath_card dag (before_subset G D i) (newEdges_on_path G D i)
  simp only [h, sum_add_distrib, sum_newEdges_card, sum_const, card_univ, Fintype.card_fin,
    smul_eq_mul, mul_one]

private theorem compressed_exit {G : Arcs V} (dag : IsDAG G) {D : List (V × V)}
    {i : Fin D.length} {u v : V} (h : CompressedBefore G D i u v) :
    ∃ e ∈ newEdges G D i, e.1 = u ∧ Reach G e.2 v :=
  markedPath_exit dag (before_subset G D i) (newEdges_on_path G D i) h

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
  let rev : Bridge (CompressedBefore (reverseArcs G) (D.map Prod.swap)) k := b.reverse
  simpa [rev, Bridge.reverse, Function.comp_def, Fin.rev_zero] using
    no_earlier_first_arc (reverseArcs_dag dag) rev

end OnlineReachabilityPreservers
