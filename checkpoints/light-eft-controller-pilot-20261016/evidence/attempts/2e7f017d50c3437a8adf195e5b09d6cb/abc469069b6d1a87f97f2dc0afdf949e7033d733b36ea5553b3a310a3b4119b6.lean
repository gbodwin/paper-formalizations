import LightEFTSpanners.NativeSeedDemand
import LightEFTSpanners.NativeEulerianForestPacking

namespace LightEFTSpanners.NativeWeighted
open Finset SimpleGraph MultigraphCuts EvenSplitting
variable {V E : Type*}
attribute [local instance] Classical.propDecidable

/-- Two labeled copies of each original edge on the actual vertex subtype.
The full-vertex hypothesis is true by construction, not assumed of ambient V. -/
def doubled (G : Graph V E) : Graph G.vertexSet (E × Fin 2) where
  vertexSet := Set.univ
  edgeSet := {d | d.1 ∈ G.edgeSet}
  IsLink d u v := G.IsLink d.1 u.val v.val
  isLink_symm := by intro d _; exact ⟨fun _ _ h => h.symm⟩
  eq_or_eq_of_isLink_of_isLink := by
    intro d u v x y h h'
    exact (h.left_eq_or_eq h').imp Subtype.ext Subtype.ext
  edge_mem_iff_exists_isLink := by
    intro d
    constructor
    · intro hd
      obtain ⟨u,v,hl⟩ := G.exists_isLink_of_mem_edgeSet hd
      exact ⟨⟨u,hl.left_mem⟩,⟨v,hl.right_mem⟩,hl⟩
    · rintro ⟨u,v,hl⟩
      exact hl.edge_mem
  left_mem_of_isLink := by intro d u v _; trivial

/-- The doubled graph's actual vertices are exactly the original actual ones. -/
def doubledVertexEquiv (G : Graph V E) : G.vertexSet ≃ (doubled G).vertexSet where
  toFun u := ⟨u, Set.mem_univ _⟩
  invFun u := u.val
  left_inv _ := rfl
  right_inv _ := rfl

theorem doubled_inc (G : Graph V E) (d : E × Fin 2) (u : G.vertexSet) :
    (doubled G).Inc d u ↔ G.Inc d.1 u.val := by
  constructor
  · rintro ⟨v,h⟩
    exact ⟨v.val,h⟩
  · rintro ⟨v,h⟩
    exact ⟨⟨v,h.right_mem⟩,h⟩

/-- Each original degree contribution, including a loop's contribution two,
is counted twice. -/
theorem doubled_degree [Fintype E] (G : Graph V E) (u : G.vertexSet) :
    nativeDegree (doubled G) u = nativeDegree G u.val + nativeDegree G u.val := by
  classical
  simp only [nativeDegree, Fintype.sum_prod_type, Fin.sum_univ_two, doubled_inc]
  change (∑ e : E, ((if G.IsLink e u.val u.val then (2:ℤ) else if G.Inc e u.val then 1 else 0) +
    (if G.IsLink e u.val u.val then (2:ℤ) else if G.Inc e u.val then 1 else 0))) = _
  exact sum_add_distrib

theorem doubled_even [Fintype E] (G : Graph V E) (u : G.vertexSet) :
    Even (nativeDegree (doubled G) u) := ⟨nativeDegree G u.val, doubled_degree G u⟩

/-- Losing both copies is necessary to block an original ID. Thus fewer than
2*k copied faults leave fewer than k fully blocked original identities. -/
theorem doubled_faultConnected [Fintype E] (G : Graph V E) {k : ℕ} {u v : G.vertexSet}
    (h : FaultConnected G k u v) :
    FaultConnected (doubled G) (2*k) (doubledVertexEquiv G u) (doubledVertexEquiv G v) := by
  classical
  intro F hF
  let B : Finset E := univ.filter fun e => ∀ i : Fin 2, (e,i) ∈ F
  have hsub : B ×ˢ (univ : Finset (Fin 2)) ⊆ F := by
    intro d hd
    exact (mem_filter.mp (mem_product.mp hd).1).2 d.2
  have hcard : B.card < k := by
    have hh := card_le_card hsub
    rw [card_product] at hh
    simp only [card_univ, Fintype.card_fin] at hh
    omega
  obtain ⟨p⟩ := h B hcard
  have lift : ∀ {x y : G.vertexSet}, (G.deleteEdges (B : Set E)).toSimpleGraph.Walk x y →
      ((doubled G).deleteEdges (F : Set (E × Fin 2))).toSimpleGraph.Reachable
        (doubledVertexEquiv G x) (doubledVertexEquiv G y) := by
    intro x y p
    induction p with
    | nil => exact Reachable.rfl
    | @cons x y z hadj p ih =>
      obtain ⟨hne,e,hl,hB⟩ := hadj
      have hi : ∃ i : Fin 2, (e,i) ∉ F := by
        by_contra! hn
        exact hB (mem_filter.mpr ⟨mem_univ _,hn⟩)
      obtain ⟨i,hi⟩ := hi
      have ha : ((doubled G).deleteEdges (F : Set (E × Fin 2))).toSimpleGraph.Adj
          (doubledVertexEquiv G x) (doubledVertexEquiv G y) :=
        ⟨fun heq => hne ((doubledVertexEquiv G).injective heq), (e,i), hl, hi⟩
      exact ha.reachable.trans ih
  exact lift p

/-- Project selected copied edges to original IDs; all vertices remain the
same original actual vertices. This assertion concerns reachability only. -/
theorem doubled_reachable_project (G : Graph V E) (C : Set (E × Fin 2))
    {u v : (doubled G).vertexSet}
    (h : ((doubled G).restrict C).toSimpleGraph.Reachable u v) :
    (G.restrict (Prod.fst '' C)).toSimpleGraph.Reachable u.val v.val := by
  obtain ⟨p⟩ := h
  induction p with
  | nil => exact Reachable.rfl
  | @cons u v z hadj p ih =>
    obtain ⟨hne,d,hd,hl⟩ := hadj
    have ha : (G.restrict (Prod.fst '' C)).toSimpleGraph.Adj u.val v.val :=
      ⟨fun heq => hne (Subtype.ext heq), d.1, ⟨d,hd,rfl⟩, hl⟩
    exact ha.reachable.trans ih

/-- At most two edge-disjoint copied members can project to a fixed original
ID, even if one member contains both copies. -/
theorem projection_congestion [Fintype E] {k : ℕ} (C : Fin k → Set (E × Fin 2))
    (hd : Pairwise (fun i j => Disjoint (C i) (C j))) (B : Fin k → Finset E)
    (hB : ∀ i, (B i : Set E) ⊆ Prod.fst '' C i) (e : E) :
    (univ.filter fun i => e ∈ B i).card ≤ 2 := by
  classical
  have hex (i : {i : Fin k // e ∈ B i}) : ∃ b : Fin 2, (e,b) ∈ C i.val := by
    obtain ⟨⟨a,b⟩,hc,heq⟩ := hB i.val i.property
    change a = e at heq
    subst a
    exact ⟨b,hc⟩
  let f : {i : Fin k // e ∈ B i} → Fin 2 := fun i => (hex i).choose
  have hf : Function.Injective f := by
    intro i j hij
    apply Subtype.ext
    by_contra hne
    have hi := (hex i).choose_spec
    have hj := (hex j).choose_spec
    change (e,f i) ∈ C i.val at hi
    change (e,f j) ∈ C j.val at hj
    rw [hij] at hi
    exact Set.disjoint_left.mp (hd hne) hi hj
  have hc := Fintype.card_le_of_injective f hf
  simpa only [Fintype.card_subtype, Fintype.card_fin] using hc

end LightEFTSpanners.NativeWeighted
