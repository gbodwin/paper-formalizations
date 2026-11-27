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


section Seven

/-- Two retained comparisons on different parents cannot return across
distinct pieces in the opposite direction to their common parent. -/
def NoCrossedTwoStepReturn (paths : I → List V) (pieces : J → List V)
    (parent : J → I) : Prop :=
  ∀ ⦃i j a c : J⦄ ⦃x y z : V⦄, i ≠ j → parent i = parent j →
    parent i ≠ parent a → parent i ≠ parent c → parent a ≠ parent c →
    x ∈ pieces i → y ∈ pieces j → ListBefore paths (parent i) y x →
    ListBefore pieces a x z → ListBefore pieces c z y → False

private abbrev sevenNearby (i j : Fin 7) : Prop :=
  j = i+1 ∨ i = j+1 ∨ j = (i+1)+1 ∨ i = (j+1)+1

private theorem seven_near_or_three (i j : Fin 7) (apart : i ≠ j) :
    sevenNearby i j ∨ j = i+3 ∨ i = j+3 := by
  unfold sevenNearby
  revert i j
  decide

private theorem injective_four_tuple {T : Type*} {a b c d : T}
    (ab : a ≠ b) (ac : a ≠ c) (ad : a ≠ d)
    (bc : b ≠ c) (bd : b ≠ d) (cd : c ≠ d) :
    Function.Injective (![a,b,c,d] : Fin 4 → T) := by
  intro i j same
  fin_cases i <;> fin_cases j <;> simp_all

private theorem forbid_four_steps {paths : I → List V} (free : BridgeFree (ListBefore paths) 4)
    (v : Fin 4 → V) (a : Fin 4 → I) (distinctV : Function.Injective v)
    (distinctA : Function.Injective a)
    (e0 : ListBefore paths (a 0) (v 0) (v 1))
    (e1 : ListBefore paths (a 1) (v 1) (v 2))
    (e2 : ListBefore paths (a 2) (v 2) (v 3))
    (river : ListBefore paths (a 3) (v 0) (v 3)) : False := by
  apply (free (k := 2) (by decide)).false
  refine ⟨v, a ∘ Fin.castSucc, a 3, distinctV, distinctA.comp (Fin.castSucc_injective 3),
    ?_, river, ?_⟩
  · intro i equal
    have indices := distinctA equal
    have vals := congrArg Fin.val indices
    have bound := i.isLt
    simp only [Fin.val_castSucc] at vals
    omega
  · intro i
    fin_cases i
    · exact e0
    · exact e1
    · exact e2

/-- Under the one-step and two-step return tests, contiguous disjoint
pieces of full-four-free parents lift any seven-bridge to its parents. -/
def listBridge_after_contiguous_opposite_safe_split_seven {paths : I → List V} {pieces : J → List V}
    [LinearOrder I] (parent : J → I)
    (steps : ∀ {i x y}, ListBefore pieces i x y → ListBefore paths (parent i) x y)
    (disjoint : ∀ {i j x}, i ≠ j → parent i = parent j → x ∈ pieces i → x ∈ pieces j → False)
    (together : ∀ {i j q x y}, parent i = parent j → parent i ≠ parent q →
      ListBefore paths (parent i) x y → ListBefore pieces q y x → x ∈ pieces i → y ∈ pieces j → i = j)
    (ordered : ∀ {i j}, i ≠ j → parent i = parent j →
      (∀ {x y}, x ∈ pieces i → y ∈ pieces j → ListBefore paths (parent i) x y) ∨
      (∀ {x y}, x ∈ pieces i → y ∈ pieces j → ListBefore paths (parent i) y x))
    (noTwo : NoCrossedTwoStepReturn paths pieces parent)
    (free : BridgeFree (ListBefore paths) 4) (b : Bridge (ListBefore pieces) 5) :
    Bridge (ListBefore paths) 5 := by
  let s := bridgeSlots b
  let p (i : Fin 7) := parent (s i)
  let v := b.vertex
  have meet := bridgeSlots_corners b (paths := pieces) id (fun {_ _ _} h => h)
  have splitDifferent {i j : Fin 7} (apart : i ≠ j) : s i ≠ s j :=
    fun eq => apart (bridgeSlots_injective b eq)
  have nearby := bridgeSlots_parent_near parent (fun {_ _ _} => steps)
    (fun {_ _ _} => disjoint)
    (fun _ {_ _ _ _} different first second => no_parallel_list_steps free.halfFree (by decide) different first second)
    (fun _ {_ _ _ _ _} => together) b
  have near (i j : Fin 7) (h : sevenNearby i j) : p i ≠ p j := by
    rcases h with rfl | rfl | rfl | rfl
    · exact nearby.1 i
    · exact (nearby.1 j).symm
    · exact nearby.2 (by decide) i (by revert i; decide)
    · exact (nearby.2 (by decide) j (by revert j; decide)).symm
  have e0 : ListBefore paths (p 0) (v 0) (v 1) := steps (b.arcStep 0)
  have e1 : ListBefore paths (p 1) (v 1) (v 2) := steps (b.arcStep 1)
  have e2 : ListBefore paths (p 2) (v 2) (v 3) := steps (b.arcStep 2)
  have e3 : ListBefore paths (p 3) (v 3) (v 4) := steps (b.arcStep 3)
  have e4 : ListBefore paths (p 4) (v 4) (v 5) := steps (b.arcStep 4)
  have e5 : ListBefore paths (p 5) (v 5) (v 6) := steps (b.arcStep 5)
  have river : ListBefore paths (p 6) (v 0) (v 6) := steps b.riverStep
  have noThree (old : Bridge (ListBefore paths) 1) : False := (free (by decide)).false old

  -- When the intervening two slots are forward arcs, a repeated parent
  -- yields either a size-three bridge or a crossed two-step return.
  have no03 : p 0 ≠ p 3 := by
    intro equal
    have apart := splitDifferent (by decide : (0 : Fin 7) ≠ 3)
    rcases ordered apart equal with earlier | later
    · exact noThree (threeListBridge (near 1 2 (by decide))
        (near 0 1 (by decide)) (near 0 2 (by decide)) e1 e2 (earlier (meet 0).2 (meet 3).1))
    · exact noTwo apart equal (near 0 1 (by decide)) (near 0 2 (by decide))
        (near 1 2 (by decide)) (meet 0).2 (meet 3).1 (later (meet 0).2 (meet 3).1)
        (b.arcStep 1) (b.arcStep 2)
  have no14 : p 1 ≠ p 4 := by
    intro equal
    have apart := splitDifferent (by decide : (1 : Fin 7) ≠ 4)
    rcases ordered apart equal with earlier | later
    · exact noThree (threeListBridge (near 2 3 (by decide))
        (near 1 2 (by decide)) (near 1 3 (by decide)) e2 e3 (earlier (meet 1).2 (meet 4).1))
    · exact noTwo apart equal (near 1 2 (by decide)) (near 1 3 (by decide))
        (near 2 3 (by decide)) (meet 1).2 (meet 4).1 (later (meet 1).2 (meet 4).1)
        (b.arcStep 2) (b.arcStep 3)
  have no25 : p 2 ≠ p 5 := by
    intro equal
    have apart := splitDifferent (by decide : (2 : Fin 7) ≠ 5)
    rcases ordered apart equal with earlier | later
    · exact noThree (threeListBridge (near 3 4 (by decide))
        (near 2 3 (by decide)) (near 2 4 (by decide)) e3 e4 (earlier (meet 2).2 (meet 5).1))
    · exact noTwo apart equal (near 2 3 (by decide)) (near 2 4 (by decide))
        (near 3 4 (by decide)) (meet 2).2 (meet 5).1 (later (meet 2).2 (meet 5).1)
        (b.arcStep 3) (b.arcStep 4)

  -- A gap containing the river gives a size-three bridge in either order.
  have no04 : p 0 ≠ p 4 := by
    intro equal
    rcases ordered (splitDifferent (by decide : (0 : Fin 7) ≠ 4)) equal with earlier | later
    · exact noThree (threeListBridge (near 0 5 (by decide))
        (near 6 0 (by decide)) (near 6 5 (by decide)) (earlier (meet 0).1 (meet 4).2) e5 river)
    · exact noThree (threeListBridge (near 0 6 (by decide))
        (near 5 0 (by decide)) (near 5 6 (by decide)) (later (meet 0).1 (meet 4).2) river e5)
  have no15 : p 1 ≠ p 5 := by
    intro equal
    rcases ordered (splitDifferent (by decide : (1 : Fin 7) ≠ 5)) equal with earlier | later
    · exact noThree (threeListBridge (near 0 1 (by decide))
        (near 6 0 (by decide)) (near 6 1 (by decide)) e0 (earlier (meet 1).1 (meet 5).2) river)
    · exact noThree (threeListBridge (near 6 1 (by decide))
        (near 0 6 (by decide)) (near 0 1 (by decide)) river (later (meet 1).1 (meet 5).2) e0)

  -- If the river's parent repeats, one side gives the shorter bridge.
  have no26 : p 2 ≠ p 6 := by
    intro equal
    rcases ordered (splitDifferent (by decide : (2 : Fin 7) ≠ 6)) equal with earlier | later
    · have lastDifferent : p 5 ≠ p 2 := fun eq => near 5 6 (by decide) (eq.trans equal)
      exact forbid_four_steps free (v ∘ ![3,4,5,6]) ![p 3,p 4,p 5,p 2]
        (b.distinctVertices.comp (injective_four_tuple (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide)))
        (injective_four_tuple (near 3 4 (by decide)) (near 3 5 (by decide)) (near 3 2 (by decide))
          (near 4 5 (by decide)) (near 4 2 (by decide)) lastDifferent)
        e3 e4 e5 (earlier (meet 2).2 (meet 6).1)
    · exact noThree (threeListBridge (near 0 1 (by decide))
        (near 2 0 (by decide)) (near 2 1 (by decide)) e0 e1 (later (meet 2).1 (meet 6).2))
  have no36 : p 3 ≠ p 6 := by
    intro equal
    rcases ordered (splitDifferent (by decide : (3 : Fin 7) ≠ 6)) equal with earlier | later
    · exact noThree (threeListBridge (near 4 5 (by decide))
        (near 3 4 (by decide)) (near 3 5 (by decide)) e4 e5 (earlier (meet 3).2 (meet 6).1))
    · have firstDifferent : p 0 ≠ p 3 := fun eq => near 0 6 (by decide) (eq.trans equal)
      exact forbid_four_steps free (v ∘ ![0,1,2,3]) ![p 0,p 1,p 2,p 3]
        (b.distinctVertices.comp (injective_four_tuple (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide)))
        (injective_four_tuple (near 0 1 (by decide)) (near 0 2 (by decide)) firstDifferent
          (near 1 2 (by decide)) (near 1 3 (by decide)) (near 2 3 (by decide)))
        e0 e1 e2 (later (meet 3).1 (meet 6).2)

  have distanceThree (i : Fin 7) : p i ≠ p (i+3) := by
    fin_cases i
    exacts [no03, no14, no25, no36, no04.symm, no15.symm, no26.symm]
  have parentInjective : Function.Injective p := by
    intro i j same
    by_contra apart
    rcases seven_near_or_three i j apart with close | rfl | rfl
    · exact near i j close same
    · exact distanceThree i same
    · exact distanceThree j same.symm
  exact liftBridgeOfInjectiveSlots parent (fun {_ _ _} => steps) b parentInjective

/-- Contiguous disjoint pieces preserve full exclusion through seven
when every opposite step stays on one piece and the two-step test holds. -/
theorem fullBridgeFree_of_contiguous_split_seven {paths : I → List V} {pieces : J → List V}
    [LinearOrder I] (parent : J → I)
    (steps : ∀ {i x y}, ListBefore pieces i x y → ListBefore paths (parent i) x y)
    (disjoint : ∀ {i j x}, i ≠ j → parent i = parent j → x ∈ pieces i → x ∈ pieces j → False)
    (together : ∀ {i j q x y}, parent i = parent j → parent i ≠ parent q →
      ListBefore paths (parent i) x y → ListBefore pieces q y x → x ∈ pieces i → y ∈ pieces j → i = j)
    (ordered : ∀ {i j}, i ≠ j → parent i = parent j →
      (∀ {x y}, x ∈ pieces i → y ∈ pieces j → ListBefore paths (parent i) x y) ∨
      (∀ {x y}, x ∈ pieces i → y ∈ pieces j → ListBefore paths (parent i) y x))
    (noTwo : NoCrossedTwoStepReturn paths pieces parent)
    (free : BridgeFree (ListBefore paths) 7) : BridgeFree (ListBefore pieces) 7 := by
  intro d cutoff
  refine ⟨fun b => ?_⟩
  have three : BridgeFree (ListBefore paths) 3 := fun _ h => free (h.trans (by decide))
  have four : BridgeFree (ListBefore paths) 4 := fun _ h => free (h.trans (by decide))
  by_cases short : d ≤ 3
  · exact (free cutoff).false (listBridge_after_opposite_safe_split_through_five parent
      (fun {_ _ _} => steps) (fun {_ _ _} => disjoint)
      (fun _ {_ _ _ _} different first second =>
        no_parallel_list_steps free.halfFree (by decide) different first second)
      (fun _ {_ _ _ _ _} => together) short b)
  · have remaining : d = 4 ∨ d = 5 := by omega
    rcases remaining with rfl | rfl
    · exact (free cutoff).false (listBridge_after_contiguous_opposite_safe_split_six parent
        (fun {_ _ _} => steps) (fun {_ _ _} => disjoint) (fun {_ _ _ _ _} => together)
        (fun {_ _} => ordered) three b)
    · exact (free cutoff).false (listBridge_after_contiguous_opposite_safe_split_seven parent
        (fun {_ _ _} => steps) (fun {_ _ _} => disjoint) (fun {_ _ _ _ _} => together)
        (fun {_ _} => ordered) noTwo four b)

end Seven

end OnlineReachabilityPreservers
