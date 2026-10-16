import LightEFTSpanners.NativeWeightedFaults
import LightEFTSpanners.NativeForestPacking

/-! Full-walk integration of native weighted fault semantics. Forgetting edge
IDs is permitted only after restriction and deletion, and only for existence
of walks, not their weights. -/
namespace LightEFTSpanners.NativeWeighted
open Finset SimpleGraph
variable {V E : Type*}

/-- Restriction retains precisely the original actual vertices. -/
def restrictVertexEquiv (G : Graph V E) (H : Finset E) :
    G.vertexSet ≃ (G.restrict (H : Set E)).vertexSet where
  toFun u := ⟨u.val, u.property⟩
  invFun u := ⟨u.val, u.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Edge deletion also preserves vertices; this explicit transport changes
neither the vertex value nor the original vertex universe. -/
def survivingVertexEquiv (G : Graph V E) (H F : Finset E) :
    G.vertexSet ≃ ((G.restrict (H : Set E)).deleteEdges (F : Set E)).vertexSet where
  toFun u := ⟨u.val, u.property⟩
  invFun u := ⟨u.val, u.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- A native simple adjacency cannot represent a loop. Custom loop steps are
removed from the reachability witness, while nonloop steps keep their actual
surviving edge IDs until after restriction and deletion. -/
theorem Walk.native_reachable {G : Graph V E} {H F : Finset E} {u v : G.vertexSet}
    (p : Walk G H F u v) :
    ((G.restrict (H : Set E)).deleteEdges (F : Set E)).toSimpleGraph.Reachable
      (survivingVertexEquiv G H F u) (survivingVertexEquiv G H F v) := by
  classical
  induction p with
  | nil u => exact Reachable.rfl
  | @cons u v z e hl he hf p ih =>
    by_cases huv : u = v
    · subst v
      exact ih
    · have hadj : ((G.restrict (H : Set E)).deleteEdges (F : Set E)).toSimpleGraph.Adj
          (survivingVertexEquiv G H F u) (survivingVertexEquiv G H F v) := by
        refine ⟨?_, e, (surviving_link_iff G H F e u.val v.val).mpr ⟨hl, he, hf⟩⟩
        exact fun h => huv ((survivingVertexEquiv G H F).injective h)
      exact hadj.reachable.trans ih

/-- Every native surviving adjacency has an actual surviving edge identity.
Lifting all steps constructs a custom walk, not just a one-step equivalence. -/
theorem walk_of_native_reachable (G : Graph V E) (H F : Finset E)
    {u v : ((G.restrict (H : Set E)).deleteEdges (F : Set E)).vertexSet}
    (h : ((G.restrict (H : Set E)).deleteEdges (F : Set E)).toSimpleGraph.Reachable u v) :
    Nonempty (Walk G H F ((survivingVertexEquiv G H F).symm u)
      ((survivingVertexEquiv G H F).symm v)) := by
  obtain ⟨p⟩ := h
  induction p with
  | nil => exact ⟨.nil _⟩
  | @cons u v z hadj p ih =>
    obtain ⟨_, e, he⟩ := hadj
    obtain ⟨hl, hk, hf⟩ := (surviving_link_iff G H F e u.val v.val).mp he
    obtain ⟨r⟩ := ih
    exact ⟨.cons e hl hk hf r⟩

theorem walk_iff_native_reachable (G : Graph V E) (H F : Finset E) (u v : G.vertexSet) :
    Nonempty (Walk G H F u v) ↔
      ((G.restrict (H : Set E)).deleteEdges (F : Set E)).toSimpleGraph.Reachable
        (survivingVertexEquiv G H F u) (survivingVertexEquiv G H F v) :=
  ⟨fun ⟨p⟩ => p.native_reachable, fun h => walk_of_native_reachable G H F h⟩

/-- Fault-free custom walks recover exactly the native restricted reachability
used in the original forest-packing contract. -/
theorem walk_empty_iff_restrict (G : Graph V E) (H : Finset E) (u v : G.vertexSet) :
    Nonempty (Walk G H ∅ u v) ↔ (G.restrict (H : Set E)).toSimpleGraph.Reachable
      (restrictVertexEquiv G H u) (restrictVertexEquiv G H v) := by
  simpa only [survivingVertexEquiv, restrictVertexEquiv, Finset.coe_empty, Graph.deleteEdges_empty, Equiv.coe_fn_mk] using walk_iff_native_reachable G H ∅ u v

/-- The original native fault contract uses strict cardinality k. -/
theorem faultConnected_restrict_iff [Fintype E] (G : Graph V E) (H : Finset E)
    (k : ℕ) (u v : G.vertexSet) :
    MultigraphCuts.FaultConnected (G.restrict (H : Set E)) k
        (restrictVertexEquiv G H u) (restrictVertexEquiv G H v) ↔
      ∀ F : Finset E, F.card < k → Nonempty (Walk G H F u v) := by
  constructor
  · intro h F hF
    exact (walk_iff_native_reachable G H F u v).mpr (h F hF)
  · intro h F hF
    exact (walk_iff_native_reachable G H F u v).mp (h F hF)

/-- The at-most-q weighted fault budget is exactly the native threshold q+1,
including q=0. No shift is silently dropped. -/
theorem faultConnected_succ_iff [Fintype E] (G : Graph V E) (H : Finset E)
    (q : ℕ) (u v : G.vertexSet) :
    MultigraphCuts.FaultConnected (G.restrict (H : Set E)) (q+1)
        (restrictVertexEquiv G H u) (restrictVertexEquiv G H v) ↔
      ∀ F : Finset E, F.card ≤ q → Nonempty (Walk G H F u v) := by
  rw [faultConnected_restrict_iff]
  simp only [Nat.lt_succ_iff]

theorem faultConnected_input_iff [Fintype E] (G : Graph V E) (k : ℕ) (u v : G.vertexSet) :
    MultigraphCuts.FaultConnected G k u v ↔
      ∀ F : Finset E, F.card < k → Nonempty (Walk G (inputEdges G) F u v) := by
  classical
  simpa only [inputEdges, restrictVertexEquiv, Set.coe_toFinset, Graph.restrict_self, Equiv.coe_fn_mk] using
    faultConnected_restrict_iff G (inputEdges G) k u v

/-- Weighted connectivity preservation transports the native q+1 threshold
from the full input to the selected graph. -/
theorem IsConnectivityPreserver.faultConnected [Fintype E] {G : Graph V E}
    {H : Finset E} {q : ℕ} (h : IsConnectivityPreserver G (inputEdges G) H q)
    {u v : G.vertexSet} (hc : MultigraphCuts.FaultConnected G (q+1) u v) :
    MultigraphCuts.FaultConnected (G.restrict (H : Set E)) (q+1)
      (restrictVertexEquiv G H u) (restrictVertexEquiv G H v) := by
  apply (faultConnected_succ_iff G H q u v).mpr
  intro F hF
  exact h.2 F hF u v ((faultConnected_input_iff G (q+1) u v).mp hc F
    (Nat.lt_succ_iff.mpr hF))

/-- Exact finite-ID reformulation of the existing native forest-packing
contract. Forest and disjointness clauses retain the same native graphs;
the reachability clauses now use custom walks with unchanged vertices. -/
def HasWalkForestPacking [Fintype E] (G : Graph V E) (k : ℕ) : Prop :=
  ∃ A : Fin k → Finset E,
    (∀ c, A c ⊆ inputEdges G ∧
      ∀ e ∈ (G.restrict (A c : Set E)).edgeSet, (G.restrict (A c : Set E)).IsBridge e) ∧
    Pairwise (fun c d => Disjoint (A c) (A d)) ∧
    ∀ c (u v : G.vertexSet),
      (∀ F : Finset E, F.card < 2*k → Nonempty (Walk G (inputEdges G) F u v)) →
      Nonempty (Walk G (A c) ∅ u v)

theorem native_forestPacking_iff_walk [Fintype E] (G : Graph V E) (k : ℕ) :
    EvenSplitting.HasNativeForestPacking G k ↔ HasWalkForestPacking G k := by
  classical
  constructor
  · rintro ⟨A, hA, hd, hr⟩
    refine ⟨fun c => (A c).toFinset, ?_, ?_, ?_⟩
    · intro c
      constructor
      · intro e he
        exact Set.mem_toFinset.mpr ((hA c).1 (Set.mem_toFinset.mp he))
      · simpa using (hA c).2
    · intro c d hcd
      apply Finset.disjoint_left.mpr
      intro e he hc
      exact Set.disjoint_left.mp (hd hcd) (Set.mem_toFinset.mp he) (Set.mem_toFinset.mp hc)
    · intro c u v h
      apply (walk_empty_iff_restrict G (A c).toFinset u v).mpr
      simpa only [restrictVertexEquiv, Set.coe_toFinset, Equiv.coe_fn_mk] using hr c u v ((faultConnected_input_iff G (2*k) u v).mpr h)
  · rintro ⟨A, hA, hd, hr⟩
    refine ⟨fun c => (A c : Set E), ?_, ?_, ?_⟩
    · intro c
      refine ⟨?_, (hA c).2⟩
      intro e he
      exact Set.mem_toFinset.mp ((hA c).1 he)
    · intro c d hcd
      exact Set.disjoint_left.mpr (fun _ he hc => Finset.disjoint_left.mp (hd hcd) he hc)
    · intro c u v h
      exact (walk_empty_iff_restrict G (A c) u v).mp
        (hr c u v ((faultConnected_input_iff G (2*k) u v).mp h))

end LightEFTSpanners.NativeWeighted
