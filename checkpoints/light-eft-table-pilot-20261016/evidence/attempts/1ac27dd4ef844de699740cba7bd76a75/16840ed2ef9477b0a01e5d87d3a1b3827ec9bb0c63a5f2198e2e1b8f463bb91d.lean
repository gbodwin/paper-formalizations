import LightSpanners.CycleProjection
import LightSpanners.UnitCycleWeight

namespace LightSpanners
open SimpleGraph
variable {V W : Type*}

/-- A base cycle projects into a tree and supplies one representative of every
original vertex. The graph construction adds exactly one copy of each chord. -/
structure VertexCopies (T : SimpleGraph V) (C : SimpleGraph W) where
  projection : C →g T
  representative : V ↪ W
  projection_representative : ∀ v, projection (representative v) = v

namespace VertexCopies
variable {G T : SimpleGraph V} {C : SimpleGraph W} (D : VertexCopies T C)

def graph (G : SimpleGraph V) : SimpleGraph W := C ⊔ (G \ T).map D.representative

theorem base_le_graph (G : SimpleGraph V) : C ≤ D.graph G := le_sup_left

def weight (w : Sym2 V → ℝ) : Sym2 W → ℝ := fun e => w (Sym2.map D.projection e)

/-- Every new edge projects to an old edge. -/
def hom (hTG : T ≤ G) : D.graph G →g G where
  toFun := D.projection
  map_rel' := by
    intro a b h
    rcases h with hc | hk
    · exact hTG (D.projection.map_rel hc)
    · obtain ⟨u, v, huv, rfl, rfl⟩ := (map_adj D.representative (G \ T) a b).mp hk
      simpa only [D.projection_representative] using ((sdiff_adj G T u v).mp huv).1

@[simp] theorem project_representative_edge (e : Sym2 V) :
    Sym2.map D.projection (D.representative.sym2Map e) = e := by
  induction e using Sym2.inductionOn with
  | hf a b => simp [Function.Embedding.sym2Map_apply, D.projection_representative]

/-- Copied chords retain their original identity under projection. -/
theorem chord_projection {e : Sym2 W} (he : e ∈ (D.graph G).edgeSet)
    (heC : e ∉ C.edgeSet) :
    Sym2.map D.projection e ∈ (G \ T).edgeSet ∧
      D.representative.sym2Map (Sym2.map D.projection e) = e := by
  rw [graph, edgeSet_sup] at he
  have hk := he.resolve_left heC
  rw [edgeSet_map] at hk
  obtain ⟨d, hd, rfl⟩ := hk
  rw [D.project_representative_edge]
  exact ⟨hd, rfl⟩

/-- A copied chord has only one preimage among all edges of the new graph. -/
theorem chord_unique_projection {e d : Sym2 W}
    (he : e ∈ (D.graph G).edgeSet) (heC : e ∉ C.edgeSet)
    (hd : d ∈ (D.graph G).edgeSet)
    (heq : Sym2.map D.projection d = Sym2.map D.projection e) : d = e := by
  have hE := D.chord_projection he heC
  have hdC : d ∉ C.edgeSet := by
    intro hc
    have ht := D.projection.map_mem_edgeSet hc
    rw [heq] at ht
    have hn : Sym2.map D.projection e ∉ T.edgeSet := by
      exact (show Sym2.map D.projection e ∈ G.edgeSet ∧
        Sym2.map D.projection e ∉ T.edgeSet from by
          simpa only [edgeSet_sdiff, Set.mem_sdiff] using hE.1).2
    exact hn ht
  have hD := D.chord_projection hd hdC
  exact hD.2.symm.trans ((congrArg D.representative.sym2Map heq).trans hE.2)

theorem weight_on_base (w : Sym2 V → ℝ) (hunit : ∀ e ∈ T.edgeSet, w e = 1)
    {e : Sym2 W} (he : e ∈ C.edgeSet) : D.weight w e = 1 :=
  hunit _ (D.projection.map_mem_edgeSet he)

theorem weight_lower (hTG : T ≤ G) (w : Sym2 V → ℝ)
    (hw : ∀ e ∈ G.edgeSet, 1 ≤ w e) {e : Sym2 W}
    (he : e ∈ (D.graph G).edgeSet) : 1 ≤ D.weight w e :=
  hw _ ((D.hom hTG).map_mem_edgeSet he)

/-- The base Hamiltonian cycle becomes an actual unit spanning cycle of the
constructed graph, with all other weights at least one. -/
def unitSpanningCycle [DecidableEq W] [Fintype W] (hTG : T ≤ G)
    (w : Sym2 V → ℝ) (hunit : ∀ e ∈ T.edgeSet, w e = 1)
    (hw : ∀ e ∈ G.edgeSet, 1 ≤ w e) (B : UnitSpanningCycle C (fun _ => 1)) :
    UnitSpanningCycle (D.graph G) (D.weight w) where
  base := B.base
  cycle := B.cycle.mapLe (D.base_le_graph G)
  hamiltonian := Walk.isHamiltonianCycle_iff_isCycle_and_length_eq.mpr
    ⟨B.hamiltonian.isCycle.mapLe (D.base_le_graph G), by
      rw [Walk.length_mapLe]
      exact B.hamiltonian.length_eq⟩
  unit := by
    intro e he
    apply D.weight_on_base w hunit
    exact B.cycle.edges_subset_edgeSet (by simpa only [Walk.edges_mapLe_eq_edges] using he)
  lower := fun e he => D.weight_lower hTG w hw he

/-- Unit weights on the original tree identify the pulled-back base weights. -/
theorem base_weightedGirth (w : Sym2 V → ℝ) {g : ℝ}
    (hunit : ∀ e ∈ T.edgeSet, w e = 1)
    (hC : WeightedGirthAbove C (fun _ => 1) g) :
    WeightedGirthAbove C (D.weight w) g := by
  intro a p hp e he
  have h := hC a p hp e he
  rw [walkWeight_eq_length_of_unit (fun _ => 1) p (by simp), mul_one] at h
  rw [D.weight_on_base w hunit (p.edges_subset_edgeSet he),
    walkWeight_eq_length_of_unit (D.weight w) p
      (fun d hd => D.weight_on_base w hunit (p.edges_subset_edgeSet hd)), mul_one]
  exact h

/-- Vertex copying preserves a girth threshold whenever the base cycle does.
The proof uses a uniquely projected chord, rather than assuming a bijection
between the old and new sets of cycles. -/
theorem weightedGirthAbove [DecidableEq V] [DecidableEq W]
    (hTG : T ≤ G) (w : Sym2 V → ℝ) (g : ℝ) (hg : 0 ≤ g)
    (hunit : ∀ e ∈ T.edgeSet, w e = 1) (hw : ∀ e ∈ G.edgeSet, 1 ≤ w e)
    (hG : WeightedGirthAbove G w g) (hC : WeightedGirthAbove C (D.weight w) g) :
    WeightedGirthAbove (D.graph G) (D.weight w) g := by
  classical
  intro a p hp e he
  by_cases hall : ∀ d ∈ p.edges, d ∈ C.edgeSet
  · have h := hC a (p.transfer C hall) (by simpa using hp) e (by simpa using he)
    simpa only [walkWeight_transfer] using h
  · have hex : ∃ f ∈ p.edges, f ∉ C.edgeSet ∧ D.weight w e ≤ D.weight w f := by
      by_cases heC : e ∈ C.edgeSet
      · push Not at hall
        obtain ⟨f, hf, hfC⟩ := hall
        refine ⟨f, hf, hfC, ?_⟩
        rw [D.weight_on_base w hunit heC]
        exact D.weight_lower hTG w hw (p.edges_subset_edgeSet hf)
      · exact ⟨e, he, heC, le_rfl⟩
    obtain ⟨f, hf, hfC, hweight⟩ := hex
    have hbound := hG.cycle_projection_bound
      (fun d hd => (zero_le_one.trans (hw d hd))) (D.hom hTG) p hp hf
      (fun d hd heq => D.chord_unique_projection (p.edges_subset_edgeSet hf) hfC
        (p.edges_subset_edgeSet hd) heq)
    change g * D.weight w f < walkWeight (D.weight w) p at hbound
    exact lt_of_le_of_lt (mul_le_mul_of_nonneg_left hweight hg) hbound

end VertexCopies
end LightSpanners
