import LightEFTSpanners.NativeEdgeDoubling

namespace LightEFTSpanners.NativeWeighted
open Finset SimpleGraph MultigraphCuts EvenSplitting
variable {V E : Type*}
attribute [local instance] Classical.propDecidable

/-- Nested restrictions agree on the original actual vertex subtype when
the innermost set is already contained in the outer one. -/
theorem selected_graph_eq (G : Graph V E) (A B : Set E) (h : B ⊆ A) :
    ((G.restrict A).restrict B).toSimpleGraph = (G.restrict B).toSimpleGraph := by
  ext u v
  constructor
  · rintro ⟨hne,e,he,_,hl⟩
    exact ⟨hne,e,he,hl⟩
  · rintro ⟨hne,e,he,hl⟩
    exact ⟨hne,e,he,h he,hl⟩

theorem selected_toFinset_graph [Fintype E] (G : Graph V E) (B : Set E) :
    (G.restrict (B.toFinset : Set E)).toSimpleGraph = (G.restrict B).toSimpleGraph := by
  classical
  ext u v
  constructor
  · rintro ⟨hne,e,he,hl⟩
    exact ⟨hne,e,Set.mem_toFinset.mp he,hl⟩
  · rintro ⟨hne,e,he,hl⟩
    exact ⟨hne,e,Set.mem_toFinset.mpr he,hl⟩

/-- Apply the existing Eulerian existence theorem to the doubled actual-vertex
graph. Project each packed member and select an actual original-ID spanning
forest inside that projection. Reachability and congestion two are retained. -/
theorem exists_doubled_projected_forests [Fintype V] [Fintype E] (G : Graph V E) (k : ℕ) :
    ∃ C : Fin k → Set (E × Fin 2),
      (∀ c, C c ⊆ (doubled G).edgeSet ∧
        ∀ d ∈ ((doubled G).restrict (C c)).edgeSet, ((doubled G).restrict (C c)).IsBridge d) ∧
      Pairwise (fun c d => Disjoint (C c) (C d)) ∧
      ∃ B : Fin k → Set E,
        (∀ c, B c ⊆ G.edgeSet ∧ B c ⊆ Prod.fst '' C c ∧
          ∀ e ∈ (G.restrict (B c)).edgeSet, (G.restrict (B c)).IsBridge e) ∧
        (∀ e, (univ.filter fun c => e ∈ B c).card ≤ 2) ∧
        ∀ c (u v : G.vertexSet), FaultConnected G k u v →
          (G.restrict (B c)).toSimpleGraph.Reachable u v := by
  classical
  obtain ⟨C,hC,hd,hr⟩ := exists_native_eulerian_forest_packing (doubled G) k rfl (doubled_even G)
  choose B hB hforest hreach using fun c =>
    exists_native_spanning_forest (G.restrict (Prod.fst '' C c))
  have hproj (c) : B c ⊆ Prod.fst '' C c := fun _ he => (hB c he).2
  have heq (c) : (G.restrict (Prod.fst '' C c)).restrict (B c) = G.restrict (B c) := by
    rw [Graph.restrict_restrict, Set.inter_eq_right.mpr (hproj c)]
  refine ⟨C,hC,hd,B,?_,?_,?_⟩
  · intro c
    exact ⟨fun _ he => (hB c he).1, hproj c, by simpa only [heq c] using hforest c⟩
  · intro e
    have hc := projection_congestion C hd (fun c => (B c).toFinset)
      (fun c => by simpa only [Set.coe_toFinset] using hproj c) e
    simpa only [Set.mem_toFinset] using hc
  · intro c u v h
    have hp := doubled_reachable_project G (C c)
      (hr c (doubledVertexEquiv G u) (doubledVertexEquiv G v) (doubled_faultConnected G h))
    have hb : ((G.restrict (Prod.fst '' C c)).restrict (B c)).toSimpleGraph.Reachable u v := by
      rw [hreach c]
      exact hp
    rw [selected_graph_eq G _ _ (hproj c)] at hb
    exact hb

/-- Native seed-to-forest interface. Every omitted actual edge is connected in
each of q+1 original-ID forests inside the seed; each seed ID belongs to at
most two members. The copied packing and the projection inclusions are explicit.
No minimum-weight assumption or weighted upper bound is needed or claimed. -/
theorem exists_seed_forests [Fintype V] [Fintype E] (G : Graph V E) (H : Finset E) (q : ℕ)
    (hH : IsConnectivityPreserver G (inputEdges G) H q) :
    ∃ C : Fin (q+1) → Set (E × Fin 2),
      (∀ c, C c ⊆ (doubled (G.restrict (H : Set E))).edgeSet ∧
        ∀ d ∈ ((doubled (G.restrict (H : Set E))).restrict (C c)).edgeSet,
          ((doubled (G.restrict (H : Set E))).restrict (C c)).IsBridge d) ∧
      Pairwise (fun c d => Disjoint (C c) (C d)) ∧
      ∃ B : Fin (q+1) → Set E,
        (∀ c, B c ⊆ (H : Set E) ∧ B c ⊆ Prod.fst '' C c ∧
          ∀ e ∈ (G.restrict (B c)).edgeSet, (G.restrict (B c)).IsBridge e) ∧
        (∀ e, (univ.filter fun c => e ∈ B c).card ≤ 2) ∧
        ∀ c (u v : G.vertexSet) e, G.IsLink e u.val v.val → e ∉ H →
          Nonempty (Walk G (B c).toFinset ∅ u v) := by
  classical
  obtain ⟨C,hC,hd,B,hB,hcong,hconn⟩ := exists_doubled_projected_forests (G.restrict (H : Set E)) (q+1)
  have hsub (c) : B c ⊆ (H : Set E) := fun _ he => ((hB c).1 he).2
  have heq (c) : (G.restrict (H : Set E)).restrict (B c) = G.restrict (B c) := by
    rw [Graph.restrict_restrict, Set.inter_eq_right.mpr (hsub c)]
  refine ⟨C,hC,hd,B,?_,hcong,?_⟩
  · intro c
    exact ⟨hsub c,(hB c).2.1,by simpa only [heq c] using (hB c).2.2⟩
  · intro c u v e he homit
    have hr := hconn c (restrictVertexEquiv G H u) (restrictVertexEquiv G H v)
      (omitted_edge_faultConnected G H q hH he homit)
    change ((G.restrict (H : Set E)).restrict (B c)).toSimpleGraph.Reachable u v at hr
    rw [selected_graph_eq G _ _ (hsub c)] at hr
    apply (walk_empty_iff_restrict G (B c).toFinset u v).mpr
    change (G.restrict ((B c).toFinset : Set E)).toSimpleGraph.Reachable u v
    rw [selected_toFinset_graph]
    exact hr

end LightEFTSpanners.NativeWeighted
