import LightSpanners.BucketRestriction

set_option backward.isDefEq.respectTransparency.types false

namespace LightSpanners.UnitSpanningCycle
open SimpleGraph Finset
attribute [local instance] Classical.propDecidable
variable {V : Type*} [DecidableEq V] [Fintype V] {G : SimpleGraph V} {w : Sym2 V → ℝ}
    (C : LightSpanners.UnitSpanningCycle G w)

/-- Retain the spanning cycle deterministically and only the selected chords. -/
noncomputable def retainedGraph (S : Finset (Sym2 V)) : SimpleGraph V :=
  G.deleteEdges {e | e∉C.cycle.edges ∧ e∉S}

theorem retainedGraph_le (S : Finset (Sym2 V)) : C.retainedGraph S≤G := deleteEdges_le _

@[simp] theorem mem_retainedGraph (S : Finset (Sym2 V)) (e : Sym2 V) :
    e∈(C.retainedGraph S).edgeSet ↔ e∈G.edgeSet ∧ (e∈C.cycle.edges ∨ e∈S) := by
  simp only [retainedGraph,edgeSet_deleteEdges,Set.mem_sdiff,Set.mem_setOf_eq]
  tauto

/-- The actual old Hamiltonian cycle survives the chord restriction. -/
noncomputable def retainedCycle (S : Finset (Sym2 V)) : UnitSpanningCycle (C.retainedGraph S) w where
  base := C.base
  cycle := C.cycle.transfer (C.retainedGraph S)
    (fun e he => (C.mem_retainedGraph S e).mpr ⟨C.cycle.edges_subset_edgeSet he,Or.inl he⟩)
  hamiltonian := Walk.isHamiltonianCycle_iff_isCycle_and_length_eq.mpr
    ⟨by exact C.hamiltonian.isCycle.transfer _,
      by rw [Walk.length_transfer]; exact C.hamiltonian.length_eq⟩
  unit := by intro e he; exact C.unit e (by rwa [Walk.edges_transfer] at he)
  lower := by intro e he; exact C.lower e ((C.mem_retainedGraph S e).mp he).1

@[simp] theorem retainedCycle_map (S : Finset (Sym2 V)) :
    (C.retainedCycle S).cycle.mapLe (C.retainedGraph_le S)=C.cycle := by
  change (C.cycle.transfer (C.retainedGraph S) _).mapLe _ = C.cycle
  rw [← Walk.transfer_eq_mapLe,Walk.transfer_transfer,Walk.transfer_self]
  apply Walk.edges_transfer _ _ ▸ C.cycle.edges_subset_edgeSet

theorem retainedCycle_darts (S : Finset (Sym2 V)) :
    (C.retainedCycle S).cycle.darts.map (liftDart (C.retainedGraph_le S))=C.cycle.darts := by
  calc
    _ = ((C.retainedCycle S).cycle.mapLe (C.retainedGraph_le S)).darts := by
      exact (Walk.darts_map _ _).symm
    _ = C.cycle.darts := congrArg Walk.darts (C.retainedCycle_map S)

/-- The total weight retained outside the cycle is exactly the finite selected sum. -/
theorem retainedGraph_noncycle_weight (S : Finset (Sym2 V))
    (hS : ∀ e∈S, e∈G.edgeSet ∧ e∉C.cycle.edges) :
    totalWeight (C.retainedGraph S) w-Fintype.card V=∑ e∈S,w e := by
  have hcyc : (C.retainedCycle S).cycle.edges=C.cycle.edges := by
    exact C.cycle_edges_lift (C.retainedCycle S) (C.retainedGraph_le S) (C.retainedCycle_darts S)
  have hset : (C.retainedGraph S).edgeFinset.filter
      (fun e => e∉(C.retainedCycle S).cycle.edges)=S := by
    ext e
    simp only [Finset.mem_filter,mem_edgeFinset,C.mem_retainedGraph,hcyc]
    constructor
    · rintro ⟨⟨_,hc|hs⟩,hn⟩
      · exact (hn hc).elim
      · exact hs
    · intro he
      exact ⟨⟨(hS e he).1,Or.inr he⟩,(hS e he).2⟩
  rw [← (C.retainedCycle S).noncycle_weight,hset]

/-- Weak counting in a retained graph yields an actual ambient-graph walk
whose every chord belongs to the selected finite set. -/
theorem weak_counting_retained (S : Finset (Sym2 V))
    (hS : ∀ e∈S, e∈G.edgeSet ∧ e∉C.cycle.edges)
    {eps : ℝ} {k : ℕ} (heps : 0<eps) (hk : 0<k)
    (hweight : 4/eps*(Fintype.card V:ℝ)≤∑ e∈S,w e) :
    ∃ (u v : V) (p : G.Walk u v), (∃ J, C.BucketMonotoneWalk eps k true J p) ∧
      k≤(C.chordEdges p).length ∧ ∀ e∈C.chordEdges p,e∈S := by
  obtain ⟨u,v,p,⟨J,hp⟩,hcount⟩ := (C.retainedCycle S).weak_counting heps hk
    (by rwa [C.retainedGraph_noncycle_weight S hS])
  refine ⟨u,v,p.mapLe (C.retainedGraph_le S),⟨J,hp.mapLe C (C.retainedCycle S)
    (C.retainedGraph_le S) (C.retainedCycle_darts S)⟩,?_,?_⟩
  · simpa only [C.chordEdges_mapLe (C.retainedCycle S) (C.retainedGraph_le S)
      (C.retainedCycle_darts S)] using hcount
  · intro e he
    have hedge : e∈p.edges ∧ e∉C.cycle.edges := by simpa [chordEdges] using he
    have hm := (C.mem_retainedGraph S e).mp (p.edges_subset_edgeSet hedge.1)
    exact hm.2.resolve_left hedge.2

end LightSpanners.UnitSpanningCycle
