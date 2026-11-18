import OnlineReachabilityPreservers.IntersectionOrder

/-! Preservation of the bridge condition under acyclic vertex and path splits. -/

namespace OnlineReachabilityPreservers

open Finset

variable {V W I J : Type*} [LinearOrder V] [LinearOrder W] [LinearOrder I] [LinearOrder J]

private def sameEndpointsBridge {paths : I → Finset V} {u v : V} {a r : I} (distinct : r ≠ a)
    (arc : PathBefore paths a u v) (river : PathBefore paths r u v) : Bridge (PathBefore paths) 0 :=
  orderedBridge ![u, v] ![a] r (by intro i j _; fin_cases i; fin_cases j; rfl)
    (fun i => by fin_cases i; exact distinct) river (fun i => by fin_cases i; exact arc)

private theorem reduce_two_arcs {paths : I → Finset V} {x y z : V} {a b r : I}
    (ra : r ≠ a) (rb : r ≠ b)
    (step₀ : PathBefore paths a x y) (step₁ : PathBefore paths b y z)
    (river : PathBefore paths r x z) :
    ∃ j ≤ 1, ∃ bridge : Bridge (PathBefore paths) j, bridge.river = r ∧ bridge.arc (Fin.last j) = b := by
  by_cases eq : a = b
  · subst a
    exact ⟨0, by decide, sameEndpointsBridge rb
      ⟨step₀.1, step₁.2.1, step₀.2.2.trans step₁.2.2⟩ river, rfl, rfl⟩
  · let bridge : Bridge (PathBefore paths) 1 :=
      orderedBridge ![x, y, z] ![a, b] r (by
        intro i j eq'
        fin_cases i <;> fin_cases j
        · rfl
        · exact (eq eq').elim
        · exact (eq eq'.symm).elim
        · rfl) (fun i => by intro; fin_cases i <;> contradiction) river
        (fun i => by fin_cases i; exacts [step₀, step₁])
    exact ⟨1, le_rfl, bridge, rfl, rfl⟩

private theorem short_detour {paths : I → Finset V} {k : ℕ} (size : k ≤ 2)
    (v : Fin (k + 2) → V) (a : Fin (k + 1) → I) (r : I)
    (different : ∀ i, r ≠ a i)
    (river : PathBefore paths r (v 0) (v (Fin.last (k + 1))))
    (step : ∀ i, PathBefore paths (a i) (v i.castSucc) (v i.succ)) :
    ∃ j ≤ k, ∃ bridge : Bridge (PathBefore paths) j,
      bridge.river = r ∧ bridge.arc (Fin.last j) = a (Fin.last k) := by
  interval_cases k
  · exact ⟨0, le_rfl, sameEndpointsBridge (different 0) (step 0) river, rfl, rfl⟩
  · exact reduce_two_arcs (different 0) (different 1) (step 0) (step 1) river
  · have s₀ : PathBefore paths (a 0) (v 0) (v 1) := step 0
    have s₁ : PathBefore paths (a 1) (v 1) (v 2) := step 1
    have s₂ : PathBefore paths (a 2) (v 2) (v 3) := step 2
    by_cases e02 : a 0 = a 2
    · let bridge := sameEndpointsBridge (different 2)
        ⟨e02 ▸ s₀.1, s₂.2.1, s₀.2.2.trans (s₁.2.2.trans s₂.2.2)⟩ river
      exact ⟨0, by decide, bridge, rfl, rfl⟩
    by_cases e01 : a 0 = a 1
    · obtain ⟨j, hj, bridge, hr, ha⟩ := reduce_two_arcs (different 1) (different 2)
        ⟨e01 ▸ s₀.1, s₁.2.1, s₀.2.2.trans s₁.2.2⟩ s₂ river
      exact ⟨j, by omega, bridge, hr, ha⟩
    by_cases e12 : a 1 = a 2
    · obtain ⟨j, hj, bridge, hr, ha⟩ := reduce_two_arcs (different 0) (different 2)
        s₀ ⟨e12 ▸ s₁.1, s₂.2.1, s₁.2.2.trans s₂.2.2⟩ river
      exact ⟨j, by omega, bridge, hr, ha⟩
    let bridge := orderedBridge v a r (by
      intro i j h
      fin_cases i <;> fin_cases j
      · rfl
      · exact (e01 h).elim
      · exact (e02 h).elim
      · exact (e01 h.symm).elim
      · rfl
      · exact (e12 h).elim
      · exact (e02 h.symm).elim
      · exact (e12 h.symm).elim
      · rfl) different river step
    exact ⟨2, le_rfl, bridge, rfl, rfl⟩

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
/-- Convex pieces of disjoint path splits project a short bridge to a short
bridge with the same parent paths for the river and the last arc. -/
theorem bridge_after_path_split {paths : I → Finset V} {pieces : J → Finset V} (parent : J → I)
    (onPath : ∀ i, pieces i ⊆ paths (parent i))
    (disjoint : ∀ i j, i ≠ j → parent i = parent j → Disjoint (pieces i) (pieces j))
    (convex_piece : ∀ i {x y z}, x ∈ pieces i → z ∈ pieces i →
      y ∈ paths (parent i) → x ≤ y → y ≤ z → y ∈ pieces i)
    {k : ℕ} (size : k ≤ 2) (b : Bridge (PathBefore pieces) k) :
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
  exact short_detour size b.vertex (parent ∘ b.arc) (parent b.river) separated
    (before b.riverStep) (fun i => before (b.arcStep i))

theorem HalfBridgeFree.split_paths {paths : I → Finset V} {pieces : J → Finset V}
    (free : HalfBridgeFree (PathBefore paths) 4) (parent : J → I) (mono : Monotone parent)
    (onPath : ∀ i, pieces i ⊆ paths (parent i))
    (disjoint : ∀ i j, i ≠ j → parent i = parent j → Disjoint (pieces i) (pieces j))
    (convex_piece : ∀ i {x y z}, x ∈ pieces i → z ∈ pieces i →
      y ∈ paths (parent i) → x ≤ y → y ≤ z → y ∈ pieces i) :
    HalfBridgeFree (PathBefore pieces) 4 := by
  intro k hk bridge earlier
  obtain ⟨j, hj, old, hr, ha⟩ := bridge_after_path_split parent onPath disjoint convex_piece
    (by omega) bridge
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
theorem BridgeFree.split_paths {paths : I → Finset V} {pieces : J → Finset V}
    (free : BridgeFree (PathBefore paths) 4) (parent : J → I)
    (onPath : ∀ i, pieces i ⊆ paths (parent i))
    (disjoint : ∀ i j, i ≠ j → parent i = parent j → Disjoint (pieces i) (pieces j))
    (convex_piece : ∀ i {x y z}, x ∈ pieces i → z ∈ pieces i →
      y ∈ paths (parent i) → x ≤ y → y ≤ z → y ∈ pieces i) :
    BridgeFree (PathBefore pieces) 4 := by
  intro k hk
  refine ⟨fun b => ?_⟩
  obtain ⟨j, hj, old, _, _⟩ :=
    bridge_after_path_split parent onPath disjoint convex_piece (by omega) b
  exact (free (by omega : j + 2 ≤ 4)).false old

end OnlineReachabilityPreservers
