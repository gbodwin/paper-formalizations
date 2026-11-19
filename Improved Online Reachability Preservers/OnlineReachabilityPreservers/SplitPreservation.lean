import OnlineReachabilityPreservers.AcyclicDetour

/-! Preservation of the bridge condition under acyclic vertex and path splits. -/

namespace OnlineReachabilityPreservers

open Finset

variable {V W I J : Type*} [LinearOrder V] [LinearOrder W] [LinearOrder I] [LinearOrder J]

omit [LinearOrder I] in
/-- A monotone vertex split preserves every bridge witness after projection,
provided each old vertex has at most one copy in each path. -/
def bridge_after_vertex_split {paths : I → Finset V} {split : I → Finset W} (project : W → V)
    (mono : Monotone project) (onPath : ∀ i, Set.MapsTo project (split i) (paths i))
    (noRepeat : ∀ i, Set.InjOn project (split i))
    {k : ℕ} (bridge : Bridge (PathBefore split) k) : Bridge (PathBefore paths) k := by
  have before {i : I} {x y : W} (h : PathBefore split i x y) : PathBefore paths i (project x) (project y) :=
    ⟨onPath i h.1, onPath i h.2.1, (mono h.2.2.le).lt_of_ne (fun e => h.2.2.ne (noRepeat i h.1 h.2.1 e))⟩
  exact orderedBridge (project ∘ bridge.vertex) bridge.arc bridge.river bridge.distinctArcs
    bridge.river_ne_arc (before bridge.riverStep) (fun i => before (bridge.arcStep i))

omit [LinearOrder J] in
/-- Convex pieces of disjoint path splits project a bridge to one of no
greater size with the same parent paths for the river and the last arc. -/
theorem bridge_after_path_split {paths : I → Finset V} {pieces : J → Finset V} (parent : J → I)
    (onPath : ∀ i, pieces i ⊆ paths (parent i))
    (disjoint : ∀ i j, i ≠ j → parent i = parent j → Disjoint (pieces i) (pieces j))
    (convex_piece : ∀ i {x y z}, x ∈ pieces i → z ∈ pieces i →
      y ∈ paths (parent i) → x ≤ y → y ≤ z → y ∈ pieces i)
    {k : ℕ} (b : Bridge (PathBefore pieces) k) :
    ∃ j ≤ k, ∃ bridge : Bridge (PathBefore paths) j,
      bridge.river = parent b.river ∧ bridge.arc (Fin.last j) = parent (b.arc (Fin.last k)) := by
  have order : StrictMono b.vertex := Fin.strictMono_iff_lt_succ.mpr fun i => (b.arcStep i).2.2
  have separated (i : Fin (k+1)) : parent b.river ≠ parent (b.arc i) := by
    intro eq
    have h := b.arcStep i
    have y_in := convex_piece b.river b.riverStep.1 b.riverStep.2.1
      (eq.symm ▸ onPath _ h.1)
      (order.monotone (Fin.zero_le _)) (order.monotone (Fin.le_last _))
    exact disjoint_left.mp (disjoint _ _ (b.river_ne_arc i) eq) y_in h.1
  have before {i : J} {u v : V} (h : PathBefore pieces i u v) : PathBefore paths (parent i) u v :=
    ⟨onPath i h.1, onPath i h.2.1, h.2.2⟩
  exact OrderedDetour.shorten_indexed b.vertex (parent ∘ b.arc) (parent b.river) separated
    (before b.riverStep) (fun i => before (b.arcStep i))

theorem HalfBridgeFree.split_paths {paths : I → Finset V} {pieces : J → Finset V} {size : ℕ}
    (free : HalfBridgeFree (PathBefore paths) size) (parent : J → I) (mono : Monotone parent)
    (onPath : ∀ i, pieces i ⊆ paths (parent i))
    (disjoint : ∀ i j, i ≠ j → parent i = parent j → Disjoint (pieces i) (pieces j))
    (convex_piece : ∀ i {x y z}, x ∈ pieces i → z ∈ pieces i →
      y ∈ paths (parent i) → x ≤ y → y ≤ z → y ∈ pieces i) :
    HalfBridgeFree (PathBefore pieces) size := by
  intro k hk bridge earlier
  obtain ⟨j, hj, old, hr, ha⟩ := bridge_after_path_split parent onPath disjoint convex_piece bridge
  apply free (by omega) old
  rw [ha, hr]
  have hne : parent (bridge.arc (Fin.last k)) ≠ parent bridge.river := by
    intro eq
    exact old.river_ne_arc (Fin.last j) (by rw [hr, ha, eq])
  exact (mono earlier.le).lt_of_ne hne

omit [LinearOrder I] in
theorem BridgeFree.split_vertices {paths : I → Finset V} {split : I → Finset W} {size : ℕ}
    (free : BridgeFree (PathBefore paths) size) (project : W → V)
    (mono : Monotone project) (onPath : ∀ i, Set.MapsTo project (split i) (paths i))
    (noRepeat : ∀ i, Set.InjOn project (split i)) : BridgeFree (PathBefore split) size := by
  intro k h
  exact ⟨fun b => (free h).false (bridge_after_vertex_split project mono onPath noRepeat b)⟩

theorem HalfBridgeFree.split_vertices {paths : I → Finset V} {split : I → Finset W} {size : ℕ}
    (free : HalfBridgeFree (PathBefore paths) size) (project : W → V)
    (mono : Monotone project) (onPath : ∀ i, Set.MapsTo project (split i) (paths i))
    (noRepeat : ∀ i, Set.InjOn project (split i)) : HalfBridgeFree (PathBefore split) size := by
  intro k h b earlier
  exact free h (bridge_after_vertex_split project mono onPath noRepeat b) earlier

omit [LinearOrder J] in
theorem BridgeFree.split_paths {paths : I → Finset V} {pieces : J → Finset V} {size : ℕ}
    (free : BridgeFree (PathBefore paths) size) (parent : J → I)
    (onPath : ∀ i, pieces i ⊆ paths (parent i))
    (disjoint : ∀ i j, i ≠ j → parent i = parent j → Disjoint (pieces i) (pieces j))
    (convex_piece : ∀ i {x y z}, x ∈ pieces i → z ∈ pieces i →
      y ∈ paths (parent i) → x ≤ y → y ≤ z → y ∈ pieces i) :
    BridgeFree (PathBefore pieces) size := by
  intro k hk
  refine ⟨fun b => ?_⟩
  obtain ⟨j, hj, old, _, _⟩ :=
    bridge_after_path_split parent onPath disjoint convex_piece b
  exact (free (by omega : j + 2 ≤ size)).false old

end OnlineReachabilityPreservers
