import OnlineReachabilityPreservers.CyclicIntersections

/-! Short bridges after path splitting when distinct paths meet at most once. -/

namespace OnlineReachabilityPreservers

variable {V I J : Type*} [DecidableEq V]

local notation "ListBefore" => SourceAudit.BeforeIn

/-- Split paths into vertex-disjoint pieces, preserving each piece's order.
If distinct parent paths meet at most once, a bridge through size four
has distinct parent paths for every arc and the river. -/
def listBridge_after_path_split {paths : I → List V} {pieces : J → List V}
    (parent : J → I)
    (steps : ∀ {i x y}, ListBefore pieces i x y → ListBefore paths (parent i) x y)
    (disjoint : ∀ {i j x}, i ≠ j → parent i = parent j → x ∈ pieces i → x ∈ pieces j → False)
    {k : ℕ} (short : k ≤ 2)
    (unique : k = 2 → ∀ {a b x y}, a ≠ b → x ∈ paths a → x ∈ paths b → y ∈ paths a → y ∈ paths b → x = y) (b : Bridge (ListBefore pieces) k) : Bridge (ListBefore paths) k := by
  refine ⟨b.vertex, parent ∘ b.arc, parent b.river, b.distinctVertices,
    ?_, ?_, steps b.riverStep, fun i => steps (b.arcStep i)⟩
  · intro i j equal
    interval_cases k
    · fin_cases i; fin_cases j; rfl
    · have one : ListBefore pieces (b.arc 0) (b.vertex 0) (b.vertex 1) := b.arcStep 0
      have two : ListBefore pieces (b.arc 1) (b.vertex 1) (b.vertex 2) := b.arcStep 1
      have apart : parent (b.arc 0) ≠ parent (b.arc 1) := fun eq =>
        disjoint (fun same => (by decide : (0 : Fin 2) ≠ 1) (b.distinctArcs same)) eq one.2.1 two.1
      change parent (b.arc i) = parent (b.arc j) at equal
      fin_cases i <;> fin_cases j <;> simp_all
    · have one : ListBefore pieces (b.arc 0) (b.vertex 0) (b.vertex 1) := b.arcStep 0
      have two : ListBefore pieces (b.arc 1) (b.vertex 1) (b.vertex 2) := b.arcStep 1
      have three : ListBefore pieces (b.arc 2) (b.vertex 2) (b.vertex 3) := b.arcStep 2
      have apart01 : parent (b.arc 0) ≠ parent (b.arc 1) := fun eq =>
        disjoint (fun same => (by decide : (0 : Fin 3) ≠ 1) (b.distinctArcs same)) eq one.2.1 two.1
      have apart12 : parent (b.arc 1) ≠ parent (b.arc 2) := fun eq =>
        disjoint (fun same => (by decide : (1 : Fin 3) ≠ 2) (b.distinctArcs same)) eq two.2.1 three.1
      have apart02 : parent (b.arc 0) ≠ parent (b.arc 2) := by
        intro eq
        have same := unique rfl apart01 (steps one).2.1 (steps two).1
          (eq.symm ▸ (steps three).1) (steps two).2.1
        exact (by decide : (1 : Fin 4) ≠ 2) (b.distinctVertices same)
      change parent (b.arc i) = parent (b.arc j) at equal
      fin_cases i <;> fin_cases j <;> simp_all
  · intro i equal
    change parent b.river = parent (b.arc i) at equal
    interval_cases k
    · fin_cases i
      exact disjoint (b.river_ne_arc 0) equal b.riverStep.1 (b.arcStep 0).1
    · have first : ListBefore pieces (b.arc 0) (b.vertex 0) (b.vertex 1) := b.arcStep 0
      have last : ListBefore pieces (b.arc 1) (b.vertex 1) (b.vertex 2) := b.arcStep 1
      fin_cases i
      · exact disjoint (b.river_ne_arc 0) equal b.riverStep.1 first.1
      · exact disjoint (b.river_ne_arc 1) equal b.riverStep.2.1 last.2.1
    · have first : ListBefore pieces (b.arc 0) (b.vertex 0) (b.vertex 1) := b.arcStep 0
      have middle : ListBefore pieces (b.arc 1) (b.vertex 1) (b.vertex 2) := b.arcStep 1
      have last : ListBefore pieces (b.arc 2) (b.vertex 2) (b.vertex 3) := b.arcStep 2
      have firstApart : parent b.river ≠ parent (b.arc 0) := fun eq =>
        disjoint (b.river_ne_arc 0) eq b.riverStep.1 first.1
      fin_cases i
      · exact firstApart equal
      · have same := unique rfl firstApart (steps b.riverStep).1 (steps first).1
          (equal.symm ▸ (steps middle).1) (steps first).2.1
        exact (by decide : (0 : Fin 4) ≠ 1) (b.distinctVertices same)
      · exact disjoint (b.river_ne_arc 2) equal b.riverStep.2.1 last.2.1

theorem BridgeFree.split_list_paths {paths : I → List V} {pieces : J → List V}
    (free : BridgeFree (ListBefore paths) 4) (parent : J → I)
    (steps : ∀ {i x y}, ListBefore pieces i x y → ListBefore paths (parent i) x y)
    (disjoint : ∀ {i j x}, i ≠ j → parent i = parent j → x ∈ pieces i → x ∈ pieces j → False)
    (unique : ∀ {a b x y}, a ≠ b → x ∈ paths a → x ∈ paths b → y ∈ paths a → y ∈ paths b → x = y) :
    BridgeFree (ListBefore pieces) 4 := by
  intro k hk
  exact ⟨fun b => (free hk).false (listBridge_after_path_split parent steps disjoint (by omega) (fun _ => unique) b)⟩

theorem HalfBridgeFree.split_list_paths [LinearOrder I] [LinearOrder J]
    {paths : I → List V} {pieces : J → List V} (free : HalfBridgeFree (ListBefore paths) 4)
    (parent : J → I) (monotone : Monotone parent)
    (steps : ∀ {i x y}, ListBefore pieces i x y → ListBefore paths (parent i) x y)
    (disjoint : ∀ {i j x}, i ≠ j → parent i = parent j → x ∈ pieces i → x ∈ pieces j → False)
    (unique : ∀ {a b x y}, a ≠ b → x ∈ paths a → x ∈ paths b → y ∈ paths a → y ∈ paths b → x = y) :
    HalfBridgeFree (ListBefore pieces) 4 := by
  intro k hk b earlier
  let old := listBridge_after_path_split parent steps disjoint (by omega) (fun _ => unique) b
  exact free hk old ((monotone earlier.le).lt_of_ne (old.river_ne_arc (Fin.last k)).symm)

/-- Through size three, disjoint order-preserving path splits work on
arbitrary locally ordered paths. -/
theorem BridgeFree.split_list_paths_short {paths : I → List V} {pieces : J → List V}
    {size : ℕ} (free : BridgeFree (ListBefore paths) size) (short : size ≤ 3) (parent : J → I)
    (steps : ∀ {i x y}, ListBefore pieces i x y → ListBefore paths (parent i) x y)
    (disjoint : ∀ {i j x}, i ≠ j → parent i = parent j → x ∈ pieces i → x ∈ pieces j → False) :
    BridgeFree (ListBefore pieces) size := by
  intro k hk
  exact ⟨fun b => (free hk).false (listBridge_after_path_split parent steps disjoint (by omega)
    (fun equal => (show False by omega).elim) b)⟩

/-- Retaining parent order also preserves the half exclusion through three. -/
theorem HalfBridgeFree.split_list_paths_short [LinearOrder I] [LinearOrder J]
    {paths : I → List V} {pieces : J → List V} {size : ℕ}
    (free : HalfBridgeFree (ListBefore paths) size) (short : size ≤ 3)
    (parent : J → I) (monotone : Monotone parent)
    (steps : ∀ {i x y}, ListBefore pieces i x y → ListBefore paths (parent i) x y)
    (disjoint : ∀ {i j x}, i ≠ j → parent i = parent j → x ∈ pieces i → x ∈ pieces j → False) :
    HalfBridgeFree (ListBefore pieces) size := by
  intro k hk b earlier
  let old := listBridge_after_path_split parent steps disjoint (by omega) (fun equal => (show False by omega).elim) b
  exact free hk old ((monotone earlier.le).lt_of_ne (old.river_ne_arc (Fin.last k)).symm)

theorem BridgeFree.split_list_paths_three {paths : I → List V} {pieces : J → List V}
    (free : BridgeFree (ListBefore paths) 3) (parent : J → I)
    (steps : ∀ {i x y}, ListBefore pieces i x y → ListBefore paths (parent i) x y)
    (disjoint : ∀ {i j x}, i ≠ j → parent i = parent j → x ∈ pieces i → x ∈ pieces j → False) :
    BridgeFree (ListBefore pieces) 3 :=
  free.split_list_paths_short le_rfl parent steps disjoint

theorem HalfBridgeFree.split_list_paths_three [LinearOrder I] [LinearOrder J]
    {paths : I → List V} {pieces : J → List V} (free : HalfBridgeFree (ListBefore paths) 3)
    (parent : J → I) (monotone : Monotone parent)
    (steps : ∀ {i x y}, ListBefore pieces i x y → ListBefore paths (parent i) x y)
    (disjoint : ∀ {i j x}, i ≠ j → parent i = parent j → x ∈ pieces i → x ∈ pieces j → False) :
    HalfBridgeFree (ListBefore pieces) 3 :=
  free.split_list_paths_short le_rfl parent monotone steps disjoint

end OnlineReachabilityPreservers
