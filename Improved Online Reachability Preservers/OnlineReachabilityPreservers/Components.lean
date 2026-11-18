import OnlineReachabilityPreservers.Growth

/-! The SCC partition and its condensation. Each component is represented by its least vertex.
The projection and lifting arguments follow the preserved SCC quotient proof for
*A Note on Distance-Preserving Graph Sparsification*. -/

namespace OnlineReachabilityPreservers

open Finset Relation

variable {V : Type*}

def SameComponent (G : Arcs V) (u v : V) : Prop := Reach G u v ∧ Reach G v u

theorem SameComponent.refl (G : Arcs V) (v : V) : SameComponent G v v := ⟨.refl, .refl⟩

theorem SameComponent.symm {G : Arcs V} {u v : V} (h : SameComponent G u v) :
    SameComponent G v u := ⟨h.2, h.1⟩

theorem SameComponent.trans {G : Arcs V} {u v w : V} (h : SameComponent G u v)
    (g : SameComponent G v w) : SameComponent G u w :=
  ⟨h.1.trans g.1, g.2.trans h.2⟩

variable [LinearOrder V] [Fintype V]

def componentVertices (G : Arcs V) (v : V) : Finset V :=
  reaches G v ∩ reaches (reverseArcs G) v

theorem mem_componentVertices {G : Arcs V} {u v : V} :
    u ∈ componentVertices G v ↔ SameComponent G u v := by
  simp [componentVertices, SameComponent, reach_reverseArcs]

def componentLabel (G : Arcs V) (v : V) : V := (least? (componentVertices G v)).getD v

theorem componentLabel_same {G : Arcs V} (v : V) :
    SameComponent G v (componentLabel G v) := by
  unfold componentLabel
  have hv : v ∈ componentVertices G v := mem_componentVertices.mpr (.refl G v)
  obtain ⟨u, hu⟩ := least?_some ⟨v, hv⟩
  rw [hu]
  exact (mem_componentVertices.mp (least?_mem hu)).symm

theorem componentLabel_eq {G : Arcs V} {u v : V} :
    componentLabel G u = componentLabel G v ↔ SameComponent G u v := by
  constructor
  · intro h
    exact (componentLabel_same u).trans (h.symm ▸ (componentLabel_same v).symm)
  · intro h
    have he : componentVertices G u = componentVertices G v := by
      ext w
      simp only [mem_componentVertices]
      exact ⟨fun hw => hw.trans h, fun hw => hw.trans h.symm⟩
    have hu : u ∈ componentVertices G u := mem_componentVertices.mpr (.refl G u)
    obtain ⟨w, hw⟩ := least?_some ⟨u, hu⟩
    have hv : least? (componentVertices G v) = some w := he ▸ hw
    simp [componentLabel, hw, hv]

@[simp]
theorem componentLabel_label (G : Arcs V) (v : V) :
    componentLabel G (componentLabel G v) = componentLabel G v :=
  componentLabel_eq.mpr (componentLabel_same v).symm

@[simp]
theorem componentLabel_reverse (G : Arcs V) (v : V) :
    componentLabel (reverseArcs G) v = componentLabel G v := by
  have he : componentVertices (reverseArcs G) v = componentVertices G v := by
    simp [componentVertices, inter_comm]
  simp [componentLabel, he]

def projectDemand (G : Arcs V) (st : V × V) : V × V :=
  (componentLabel G st.1, componentLabel G st.2)

/-- The graph of SCC labels, padded by unused isolated labels to keep the input vertex type. -/
def condensation (G : Arcs V) : Arcs V :=
  (G.filter (fun e => componentLabel G e.1 ≠ componentLabel G e.2)).image (projectDemand G)

theorem edge_condensation {G : Arcs V} {a b : V} :
    Edge (condensation G) a b ↔
    a ≠ b ∧ ∃ u v, Edge G u v ∧ componentLabel G u = a ∧ componentLabel G v = b := by
  unfold Edge condensation
  simp only [mem_image, mem_filter, Prod.exists, projectDemand, Prod.mk.injEq]
  constructor
  · rintro ⟨u, v, ⟨he, hne⟩, hu, hv⟩
    exact ⟨by simpa [hu, hv] using hne, u, v, he, hu, hv⟩
  · rintro ⟨hne, u, v, he, rfl, rfl⟩
    exact ⟨u, v, ⟨he, hne⟩, rfl, rfl⟩

/-- Project each crossing edge, and drop each step within a component. -/
theorem project_reach {G : Arcs V} {u v : V} (h : Reach G u v) :
    Reach (condensation G) (componentLabel G u) (componentLabel G v) := by
  induction h with
  | refl => exact .refl
  | @tail x y _ exy ih =>
    by_cases hxy : componentLabel G x = componentLabel G y
    · exact hxy ▸ ih
    · exact ih.tail (edge_condensation.mpr ⟨hxy, x, y, exy, rfl, rfl⟩)

theorem condensation_edge_lifts {G : Arcs V} {a b : V} (edge : Edge (condensation G) a b) :
    Reach G a b := by
  obtain ⟨_, u, v, e, rfl, rfl⟩ := edge_condensation.mp edge
  exact ((componentLabel_same u).2.tail e).trans (componentLabel_same v).1

theorem condensation_reach_lifts {G : Arcs V} {a b : V}
    (walk : Reach (condensation G) a b) : Reach G a b := by
  induction walk with
  | refl => exact .refl
  | tail _ e ih => exact ih.trans (condensation_edge_lifts e)

/-- Every nontrivial return across component labels would put them in one SCC. -/
theorem condensation_dag (G : Arcs V) : IsDAG (condensation G) := by
  intro a b edge back
  have hab := condensation_edge_lifts edge
  have hba := condensation_reach_lifts back
  obtain ⟨hne, u, v, _, hu, hv⟩ := edge_condensation.mp edge
  have ha : componentLabel G a = a := hu ▸ componentLabel_label G u
  have hb : componentLabel G b = b := hv ▸ componentLabel_label G v
  have h := componentLabel_eq.mpr (show SameComponent G a b from ⟨hab, hba⟩)
  exact hne (ha.symm.trans (h.trans hb))

end OnlineReachabilityPreservers
