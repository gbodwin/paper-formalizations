import Mathlib.Data.Fin.Tuple.Basic
import OnlineReachabilityPreservers.CyclicIntersections

/-! Lifting short bridges after disjoint order-preserving path splits. -/

namespace OnlineReachabilityPreservers

variable {V I J : Type*} [DecidableEq V]

local notation "ListBefore" => SourceAudit.BeforeIn

private def bridgeSlots {pieces : J → List V} {k : ℕ} (b : Bridge (ListBefore pieces) k) : Fin (k+2) → J :=
  Fin.snoc b.arc b.river

private theorem bridgeSlots_injective {pieces : J → List V} {k : ℕ} (b : Bridge (ListBefore pieces) k) :
    Function.Injective (bridgeSlots b) := by
  intro a c eq
  refine Fin.lastCases (motive := fun a => bridgeSlots b a = bridgeSlots b c → a = c) ?_ ?_ a eq
  · intro eq
    refine Fin.lastCases (motive := fun c => bridgeSlots b (Fin.last (k+1)) = bridgeSlots b c → _ = c) ?_ ?_ c eq
    · exact fun _ => rfl
    · intro d equal
      exact (b.river_ne_arc d (by simpa only [bridgeSlots, Fin.snoc_last, Fin.snoc_castSucc] using equal)).elim
  · intro d eq
    refine Fin.lastCases (motive := fun c => bridgeSlots b d.castSucc = bridgeSlots b c → d.castSucc = c) ?_ ?_ c eq
    · intro equal
      exact (b.river_ne_arc d (by simpa only [bridgeSlots, Fin.snoc_last, Fin.snoc_castSucc] using equal.symm)).elim
    · intro e equal
      exact congrArg Fin.castSucc (b.distinctArcs (by simpa only [bridgeSlots, Fin.snoc_castSucc] using equal))

private theorem cycleNext_castSucc {k : ℕ} (i : Fin (k+1)) :
    (i.castSucc : Fin (k+2)) + 1 = i.succ := by
  apply Fin.ext
  rw [Fin.val_add, Fin.val_one, Fin.val_castSucc, Fin.val_succ]
  exact Nat.mod_eq_of_lt (Nat.succ_lt_succ i.isLt)

private theorem cycleNext_last (k : ℕ) : (Fin.last (k+1) : Fin (k+2)) + 1 = 0 := by
  apply Fin.ext
  rw [Fin.val_add, Fin.val_one, Fin.val_last, Fin.val_zero]
  exact Nat.mod_self _

private theorem bridgeSlots_corners {paths : I → List V} {pieces : J → List V}
    {k : ℕ} (b : Bridge (ListBefore pieces) k) (parent : J → I)
    (steps : ∀ {i x y}, ListBefore pieces i x y → ListBefore paths (parent i) x y)
    (i : Fin (k+2)) : b.vertex i ∈ paths (parent (bridgeSlots b i)) ∧
      b.vertex (i+1) ∈ paths (parent (bridgeSlots b i)) := by
  refine Fin.lastCases (motive := fun i => b.vertex i ∈ paths (parent (bridgeSlots b i)) ∧
    b.vertex (i+1) ∈ paths (parent (bridgeSlots b i))) ?_ ?_ i
  · rw [bridgeSlots, Fin.snoc_last, cycleNext_last]
    exact ⟨(steps b.riverStep).2.1, (steps b.riverStep).1⟩
  · intro j
    rw [bridgeSlots, Fin.snoc_castSucc, cycleNext_castSucc]
    exact ⟨(steps (b.arcStep j)).1, (steps (b.arcStep j)).2.1⟩

private theorem cycleNext_ne {k : ℕ} (i : Fin (k+2)) : i ≠ i+1 := by
  refine Fin.lastCases (motive := fun i : Fin (k+2) => i ≠ i+1) ?_ ?_ i
  · rw [cycleNext_last]
    exact fun h => by have zero := congrArg Fin.val h; simp at zero
  · intro j
    rw [cycleNext_castSucc]
    exact fun h => by have equal := congrArg Fin.val h; simp at equal

private theorem cyclicNear {k : ℕ} (short : k ≤ 3) {i j : Fin (k+2)} (different : i ≠ j) :
    j = i+1 ∨ i = j+1 ∨ j = (i+1)+1 ∨ i = (j+1)+1 := by
  interval_cases k <;> fin_cases i <;> fin_cases j <;> first | contradiction | decide


private theorem cyclicNeighbors {k : ℕ} (short : k ≤ 1) {i j : Fin (k+2)} (different : i ≠ j) :
    j = i+1 ∨ i = j+1 := by
  interval_cases k <;> fin_cases i <;> fin_cases j <;> first | contradiction | decide

private theorem bridgeSlots_parent_near {paths : I → List V} {pieces : J → List V} {k : ℕ}
    (parent : J → I)
    (steps : ∀ {i x y}, ListBefore pieces i x y → ListBefore paths (parent i) x y)
    (disjoint : ∀ {i j x}, i ≠ j → parent i = parent j → x ∈ pieces i → x ∈ pieces j → False)
    (noParallel : 2 ≤ k → ∀ {a b x y}, a ≠ b → ListBefore paths a x y → ListBefore paths b x y → False)
    (together : 2 ≤ k → ∀ {i j q x y}, parent i = parent j → parent i ≠ parent q →
      ListBefore paths (parent i) x y → ListBefore pieces q y x → x ∈ pieces i → y ∈ pieces j → i = j)
    (b : Bridge (ListBefore pieces) k) :
    (∀ i, parent (bridgeSlots b i) ≠ parent (bridgeSlots b (i+1))) ∧
    (2 ≤ k → ∀ i, i ≠ (i+1)+1 → parent (bridgeSlots b i) ≠ parent (bridgeSlots b ((i+1)+1))) := by
  let slots := bridgeSlots b
  have meet := bridgeSlots_corners b (paths := pieces) id (fun {_ _ _} h => h)
  have meetProjected := bridgeSlots_corners b parent (fun {_ _ _} h => steps h)
  have uniqueSlots := bridgeSlots_injective b
  have neighbors (i : Fin (k+2)) : parent (slots i) ≠ parent (slots (i+1)) := by
    intro same
    have piecesApart : slots i ≠ slots (i+1) := fun eq => cycleNext_ne i (uniqueSlots eq)
    exact disjoint piecesApart same (meet i).2 (meet (i+1)).1
  have nextPair (large : 2 ≤ k) (i : Fin (k+2)) (apart : i ≠ (i+1)+1) : parent (slots i) ≠ parent (slots ((i+1)+1)) := by
    let j := i+1
    let l := j+1
    intro same
    have partsApart : slots i ≠ slots l := fun eq => apart (uniqueSlots eq)
    have cornersApart : b.vertex j ≠ b.vertex l := fun eq => cycleNext_ne j (b.distinctVertices eq)
    have left : b.vertex j ∈ pieces (slots i) := (meet i).2
    have right : b.vertex l ∈ pieces (slots l) := (meet l).1
    have oldRight : b.vertex l ∈ paths (parent (slots i)) := same.symm ▸ (meetProjected l).1
    rcases listBefore_total (meetProjected i).2 oldRight cornersApart with old | old <;>
      rcases listBefore_total (meet j).1 (meet j).2 cornersApart with current | current
    · exact noParallel large (neighbors i) old (steps current)
    · exact partsApart (together large same (neighbors i) old current left right)
    · have reverseParent : parent (slots l) ≠ parent (slots j) := same ▸ neighbors i
      exact partsApart (together large same.symm reverseParent (same ▸ old) current right left).symm
    · exact noParallel large (neighbors i) old (steps current)
  exact ⟨neighbors,nextPair⟩

private abbrev liftBridgeOfInjectiveSlots {paths : I → List V} {pieces : J → List V} {k : ℕ}
    (parent : J → I)
    (steps : ∀ {i x y}, ListBefore pieces i x y → ListBefore paths (parent i) x y)
    (b : Bridge (ListBefore pieces) k)
    (parentInjective : Function.Injective (parent ∘ bridgeSlots b)) : Bridge (ListBefore paths) k := by
  let slots := bridgeSlots b
  refine ⟨b.vertex, parent ∘ b.arc, parent b.river, b.distinctVertices,
    ?_, ?_, steps b.riverStep, fun i => steps (b.arcStep i)⟩
  · intro i j equal
    have matchSlots : (i.castSucc : Fin (k+2)) = j.castSucc := parentInjective (by
      simpa only [Function.comp_apply, slots, bridgeSlots, Fin.snoc_castSucc] using equal)
    exact Fin.ext (congrArg (fun i : Fin (k+2) => i.val) matchSlots)
  · intro i equal
    have matchSlots : (Fin.last (k+1) : Fin (k+2)) = i.castSucc := parentInjective (by
      simpa only [Function.comp_apply, slots, bridgeSlots, Fin.snoc_castSucc, Fin.snoc_last] using equal)
    have same := congrArg Fin.val matchSlots
    simp only [Fin.val_last, Fin.val_castSucc] at same
    have bound := i.isLt
    omega

/-- Around a bridge of size at most five, any two edges are neighbors or
have one intervening edge. Mirrored cuts keep their parent paths distinct. -/
def listBridge_after_opposite_safe_split_through_five {paths : I → List V} {pieces : J → List V} {k : ℕ}
    (parent : J → I)
    (steps : ∀ {i x y}, ListBefore pieces i x y → ListBefore paths (parent i) x y)
    (disjoint : ∀ {i j x}, i ≠ j → parent i = parent j → x ∈ pieces i → x ∈ pieces j → False)
    (noParallel : 2 ≤ k → ∀ {a b x y}, a ≠ b → ListBefore paths a x y → ListBefore paths b x y → False)
    (together : 2 ≤ k → ∀ {i j q x y}, parent i = parent j → parent i ≠ parent q →
      ListBefore paths (parent i) x y → ListBefore pieces q y x → x ∈ pieces i → y ∈ pieces j → i = j)
    (short : k ≤ 3) (b : Bridge (ListBefore pieces) k) : Bridge (ListBefore paths) k := by
  let slots := bridgeSlots b
  have nearby := bridgeSlots_parent_near parent (fun {_ _ _} => steps)
    (fun {_ _ _} => disjoint) (fun h {_ _ _ _} => noParallel h) (fun h {_ _ _ _ _} => together h) b
  have neighbors := nearby.1
  have nextPair := nearby.2
  have parentInjective : Function.Injective (parent ∘ slots) := by
    intro i j same
    by_contra! different
    change parent (slots i) = parent (slots j) at same
    by_cases small : k ≤ 1
    · rcases cyclicNeighbors small different with rfl | rfl
      · exact neighbors i same
      · exact neighbors j same.symm
    · have large : 2 ≤ k := by omega
      rcases cyclicNear short different with rfl | rfl | rfl | rfl
      · exact neighbors i same
      · exact neighbors j same.symm
      · exact nextPair large i different same
      · exact nextPair large j different.symm same.symm
  exact liftBridgeOfInjectiveSlots parent (fun {_ _ _} => steps) b parentInjective

private theorem cyclicNearSix (i j : Fin 6) (apart : i ≠ j) (nonopposite : j ≠ i+3) :
    j = i+1 ∨ i = j+1 ∨ j = (i+1)+1 ∨ i = (j+1)+1 := by
  revert i j
  decide

/-- A mirrored split into contiguous pieces lifts every six-bridge provided
all original full bridges through size three are excluded. -/
def listBridge_after_contiguous_opposite_safe_split_six {paths : I → List V} {pieces : J → List V}
    [LinearOrder I] (parent : J → I)
    (steps : ∀ {i x y}, ListBefore pieces i x y → ListBefore paths (parent i) x y)
    (disjoint : ∀ {i j x}, i ≠ j → parent i = parent j → x ∈ pieces i → x ∈ pieces j → False)
    (together : ∀ {i j q x y}, parent i = parent j → parent i ≠ parent q →
      ListBefore paths (parent i) x y → ListBefore pieces q y x → x ∈ pieces i → y ∈ pieces j → i = j)
    (separated : ∀ {i j}, i ≠ j → parent i = parent j →
      (∀ {x y}, x ∈ pieces i → y ∈ pieces j → ListBefore paths (parent i) x y) ∨
      (∀ {x y}, x ∈ pieces i → y ∈ pieces j → ListBefore paths (parent i) y x))
    (free : BridgeFree (ListBefore paths) 3) (b : Bridge (ListBefore pieces) 4) : Bridge (ListBefore paths) 4 := by
  let s := bridgeSlots b
  let p (i : Fin 6) := parent (s i)
  let v := b.vertex
  have meet := bridgeSlots_corners b (paths := pieces) id (fun {_ _ _} h => h)
  have separatePieces {i j : Fin 6} (apart : i ≠ j) : s i ≠ s j :=
    fun eq => apart (bridgeSlots_injective b eq)
  have nearby := bridgeSlots_parent_near parent (fun {_ _ _} => steps)
    (fun {_ _ _} => disjoint)
    (fun _ {_ _ _ _} diff one two => no_parallel_list_steps free.halfFree (by decide) diff one two)
    (fun _ {_ _ _ _ _} => together) b
  have neighbor := nearby.1
  have atTwo := nearby.2
  have near (i j : Fin 6) (apart : i ≠ j) (nonopposite : j ≠ i+3) : p i ≠ p j := by
    rcases cyclicNearSix i j apart nonopposite with rfl | rfl | rfl | rfl
    · exact neighbor _
    · exact (neighbor _).symm
    · exact atTwo (by decide) _ apart
    · exact (atTwo (by decide) _ apart.symm).symm
  have e0 : ListBefore paths (p 0) (v 0) (v 1) := steps (b.arcStep 0)
  have e1 : ListBefore paths (p 1) (v 1) (v 2) := steps (b.arcStep 1)
  have e2 : ListBefore paths (p 2) (v 2) (v 3) := steps (b.arcStep 2)
  have e3 : ListBefore paths (p 3) (v 3) (v 4) := steps (b.arcStep 3)
  have e4 : ListBefore paths (p 4) (v 4) (v 5) := steps (b.arcStep 4)
  have river : ListBefore paths (p 5) (v 0) (v 5) := steps b.riverStep
  have noThree (old : Bridge (ListBefore paths) 1) : False := (free (by decide)).false old
  have opposite0 : p 0 ≠ p 3 := by
    intro eq
    rcases separated (separatePieces (by decide : (0 : Fin 6) ≠ 3)) eq with first | last
    · exact noThree (threeListBridge (near 1 2 (by decide) (by decide))
        (near 0 1 (by decide) (by decide)) (near 0 2 (by decide) (by decide)) e1 e2
        (first (meet 0).2 (meet 3).1))
    · exact noThree (threeListBridge (near 0 5 (by decide) (by decide))
        (near 4 0 (by decide) (by decide)) (near 4 5 (by decide) (by decide))
        (last (meet 0).1 (meet 3).2) river e4)
  have opposite1 : p 1 ≠ p 4 := by
    intro eq
    rcases separated (separatePieces (by decide : (1 : Fin 6) ≠ 4)) eq with first | last
    · exact noThree (threeListBridge (near 2 3 (by decide) (by decide))
        (near 1 2 (by decide) (by decide)) (near 1 3 (by decide) (by decide)) e2 e3
        (first (meet 1).2 (meet 4).1))
    · exact noThree (threeListBridge (near 5 1 (by decide) (by decide))
        (near 0 5 (by decide) (by decide)) (near 0 1 (by decide) (by decide))
        river (last (meet 1).1 (meet 4).2) e0)
  have opposite2 : p 2 ≠ p 5 := by
    intro eq
    rcases separated (separatePieces (by decide : (2 : Fin 6) ≠ 5)) eq with first | last
    · exact noThree (threeListBridge (near 3 4 (by decide) (by decide))
        (near 2 3 (by decide) (by decide)) (near 2 4 (by decide) (by decide)) e3 e4
        (first (meet 2).2 (meet 5).1))
    · exact noThree (threeListBridge (near 0 1 (by decide) (by decide))
        (near 2 0 (by decide) (by decide)) (near 2 1 (by decide) (by decide)) e0 e1
        (last (meet 2).1 (meet 5).2))
  have parentInjective : Function.Injective p := by
    intro i j same
    by_contra apart
    by_cases antipodal : j = i+3
    · subst j
      fin_cases i
      · exact opposite0 same
      · exact opposite1 same
      · exact opposite2 same
      · exact opposite0 same.symm
      · exact opposite1 same.symm
      · exact opposite2 same.symm
    · exact near i j apart antipodal same
  exact liftBridgeOfInjectiveSlots parent (fun {_ _ _} => steps) b parentInjective

/-- A split through cutoff four can keep opposite intersections in a common block. -/
def listBridge_after_opposite_safe_split {paths : I → List V} {pieces : J → List V}
    (parent : J → I)
    (steps : ∀ {i x y}, ListBefore pieces i x y → ListBefore paths (parent i) x y)
    (disjoint : ∀ {i j x}, i ≠ j → parent i = parent j → x ∈ pieces i → x ∈ pieces j → False)
    {k : ℕ} (short : k ≤ 2)
    (noParallel : k = 2 → ∀ {a b x y}, a ≠ b → ListBefore paths a x y → ListBefore paths b x y → False)
    (together : k = 2 → ∀ {i j q x y}, parent i = parent j → parent i ≠ parent q →
      ListBefore paths (parent i) x y → ListBefore pieces q y x → x ∈ pieces i → y ∈ pieces j → i = j)
    (b : Bridge (ListBefore pieces) k) : Bridge (ListBefore paths) k := by
  exact listBridge_after_opposite_safe_split_through_five parent steps disjoint
    (fun lower => noParallel (Nat.le_antisymm short lower))
    (fun lower => together (Nat.le_antisymm short lower)) (short.trans (by decide)) b

/-- Split paths into vertex-disjoint pieces, preserving each piece's order.
If distinct parent paths meet at most once, a bridge through size four
has distinct parent paths for every arc and the river. -/
def listBridge_after_path_split {paths : I → List V} {pieces : J → List V}
    (parent : J → I)
    (steps : ∀ {i x y}, ListBefore pieces i x y → ListBefore paths (parent i) x y)
    (disjoint : ∀ {i j x}, i ≠ j → parent i = parent j → x ∈ pieces i → x ∈ pieces j → False)
    {k : ℕ} (short : k ≤ 2)
    (unique : k = 2 → ∀ {a b x y}, a ≠ b → x ∈ paths a → x ∈ paths b → y ∈ paths a → y ∈ paths b → x = y) (b : Bridge (ListBefore pieces) k) : Bridge (ListBefore paths) k := by
  refine listBridge_after_opposite_safe_split parent steps disjoint short ?_ ?_ b
  · intro size a q x y apart xy parallel
    exact listBefore_ne xy (unique size apart xy.1 parallel.1 xy.2.1 parallel.2.1)
  · intro size i j q x y _ apart xy yx _ _
    have reversed := steps yx
    exact (listBefore_ne xy (unique size apart xy.1 reversed.2.1 xy.2.1 reversed.1)).elim

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
