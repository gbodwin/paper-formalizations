import OnlineReachabilityPreservers.LocalFrozenCleaning

/-! A common partition of the vertices splits paths without creating bridges. -/

namespace OnlineReachabilityPreservers

open Finset

local notation "ListBefore" => SourceAudit.BeforeIn

variable {V I B : Type*} [LinearOrder V] [LinearOrder I] [LinearOrder B]

/-- Restrict each original path to one part, keeping the original path order
within each part and the original arrival order between different parents. -/
def partitionListPaths (paths : I → List V) (part : V → B) (piece : I ×ₗ B) : List V :=
  (paths (ofLex piece).1).filter (fun v => decide (part v = (ofLex piece).2))

omit [LinearOrder V] [LinearOrder I] in
private theorem partitionListPath_sublist (paths : I → List V) (part : V → B) (piece : I ×ₗ B) :
    List.Sublist (partitionListPaths paths part piece) (paths (ofLex piece).1) :=
  List.filter_sublist

omit [LinearOrder V] [LinearOrder I] in
private theorem partitionListPath_mem {paths : I → List V} {part : V → B} {piece : I ×ₗ B}
    {v : V} : v ∈ partitionListPaths paths part piece ↔
      v ∈ paths (ofLex piece).1 ∧ part v = (ofLex piece).2 := by
  simp only [partitionListPaths, List.mem_filter, decide_eq_true_eq]

/-- A bridge stays in one part. Within that part, projecting pieces to
parents is injective on all participating indices, including the river. -/
theorem partitionListPaths_admissible (paths : I → List V) (part : V → B)
    (simple : ∀ i, (paths i).Nodup) {half : Bool} {k : ℕ}
    (allowed : localOrderAdmissible half k paths) :
    localOrderAdmissible half k (partitionListPaths paths part) := by
  let pieces := partitionListPaths paths part
  let parent (j : I ×ₗ B) := (ofLex j).1
  let tag (j : I ×ₗ B) := (ofLex j).2
  have samePart {j : I ×ₗ B} {v : V} (inside : v ∈ pieces j) : part v = tag j :=
    (partitionListPath_mem.mp inside).2
  have project (s : ℕ) (b : Bridge (ListBefore pieces) s) :
      ∃ old : Bridge (ListBefore paths) s,
        old.river = parent b.river ∧ ∀ i, old.arc i = parent (b.arc i) := by
    have sameCorner (i : Fin (s+2)) : part (b.vertex 0) = part (b.vertex i) := by
      induction i using Fin.induction with
      | zero => rfl
      | succ i ih =>
        exact ih.trans ((samePart (b.arcStep i).1).trans (samePart (b.arcStep i).2.1).symm)
    have sameTag (i : Fin (s+1)) : tag (b.arc i) = tag b.river :=
      (samePart (b.arcStep i).1).symm.trans ((sameCorner i.castSucc).symm.trans (samePart b.riverStep.1))
    have samePiece {a c : I ×ₗ B} (p : parent a = parent c) (t : tag a = tag c) : a = c :=
      ofLex.injective (Prod.ext p t)
    have step {i : I ×ₗ B} {x y : V} (h : ListBefore pieces i x y) :
        ListBefore paths (parent i) x y :=
      listBefore_of_sublist (paths := fun j : I ×ₗ B => paths (parent j)) (cut := pieces)
        (simple (parent i)) (partitionListPath_sublist paths part i) h
    let old : Bridge (ListBefore paths) s :=
      ⟨b.vertex, parent ∘ b.arc, parent b.river, b.distinctVertices,
        fun i j same => b.distinctArcs (samePiece same ((sameTag i).trans (sameTag j).symm)),
        fun i same => b.river_ne_arc i (samePiece same (sameTag i).symm),
        step b.riverStep, fun i => step (b.arcStep i)⟩
    exact ⟨old, rfl, fun _ => rfl⟩
  cases half
  · intro s hs
    exact ⟨fun b => (allowed hs).false (project s b).choose⟩
  · intro s hs b earlier
    obtain ⟨old, river, arcs⟩ := project s b
    apply allowed hs old
    rw [river, arcs]
    rcases Prod.Lex.lt_iff.mp earlier with before | ⟨same, _⟩
    · exact before
    · exfalso
      exact old.river_ne_arc (Fin.last s) (river.trans (same.symm.trans (arcs _).symm))

variable [Fintype B]

omit [LinearOrder I] in
/-- The partition assigns every incidence to exactly one piece. -/
theorem partitionListPaths_mass (paths : I → List V) (part : V → B) [Fintype I]
    (simple : ∀ i, (paths i).Nodup) :
    ∑ piece, (partitionListPaths paths part piece).length = ∑ i, (paths i).length := by
  have rows (i : I) (b : B) : ((paths i).filter fun x => decide (part x = b)).toFinset =
      (paths i).toFinset.filter (fun x => part x = b) := by
    ext x
    simp only [List.mem_toFinset, List.mem_filter, decide_eq_true_eq, mem_filter]
  have width (i : I) (b : B) : ((paths i).filter fun x => decide (part x = b)).length =
      ((paths i).toFinset.filter (fun x => part x = b)).card := by
    rw [← rows, List.toFinset_card_of_nodup (List.filter_sublist.nodup (simple i))]
  calc
    _ = ∑ x : I × B, (partitionListPaths paths part (toLex x)).length :=
      (Equiv.sum_comp (toLex : (I × B) ≃ (I ×ₗ B)) _).symm
    _ = _ := by
      rw [Fintype.sum_prod_type]
      apply sum_congr rfl
      intro i _
      calc
        _ = ∑ b, ((paths i).toFinset.filter (fun x => part x = b)).card :=
          sum_congr rfl fun b _ => width i b
        _ = (paths i).toFinset.card :=
          (card_eq_sum_card_fiberwise (f := part) (t := (univ : Finset B)) (by simp)).symm
        _ = _ := List.toFinset_card_of_nodup (simple i)

omit [LinearOrder I] in
/-- A vertex occurs in exactly one piece of every path that contains it. -/
theorem partitionListPaths_degree (paths : I → List V) (part : V → B) [Fintype I] (v : V) :
    (occurrences (fun i => (partitionListPaths paths part i).toFinset) v).card =
      (occurrences (fun i => (paths i).toFinset) v).card := by
  let piece : I ↪ I ×ₗ B :=
    ⟨fun i => toLex (i, part v), fun i j eq => congrArg (fun k => (ofLex k).1) eq⟩
  have allPieces : occurrences (fun i => (partitionListPaths paths part i).toFinset) v =
      (occurrences (fun i => (paths i).toFinset) v).map piece := by
    ext i
    constructor
    · intro hi
      simp only [mem_occurrences, List.mem_toFinset] at hi
      obtain ⟨inside, tag⟩ := partitionListPath_mem.mp hi
      exact mem_map.mpr ⟨(ofLex i).1, mem_occurrences.mpr (List.mem_toFinset.mpr inside),
        ofLex.injective (Prod.ext rfl tag)⟩
    · rintro hi
      obtain ⟨j,inside,rfl⟩ := mem_map.mp hi
      simp only [mem_occurrences, List.mem_toFinset] at inside ⊢
      exact partitionListPath_mem.mpr ⟨inside, rfl⟩
  rw [allPieces, card_map]

/-- A shared vertex partition with bounded path lengths and room for the
pieces in the original path budget gives a frozen cleaned system. -/
theorem regularization_list_frozen_by_vertex_partition [Fintype I]
    [Fintype V] {half : Bool} {k n p M : ℕ}
    (paths : I → List V) (part : V → B) (simple : ∀ i, (paths i).Nodup)
    (allowed : localOrderAdmissible half k paths)
    (degreeCondition : (half = true → k ≤ 4) ∨
      (∀ v, (occurrences (fun i => (paths i).toFinset) v).card ≤ 4*M/n))
    (hn : 0 < n) (hp : 0 < p) (dense : n ≤ M) (long : p ≤ M)
    (vertices : Fintype.card V ≤ n) (pieces : Fintype.card I * Fintype.card B ≤ p)
    (lengthCap : ∀ i b, ((paths i).toFinset.filter (fun x => part x = b)).card ≤ 4*M/p)
    (loss : 3*M ≤ 4*(∑ i, (paths i).length)) (massCap : (∑ i, (paths i).length) ≤ M) :
    ∃ n' ≤ n, ∃ p' ≤ p, ∃ clean : Fin p' → List (Fin n'),
      (∀ i, (clean i).Nodup) ∧ localOrderAdmissible half k clean ∧
      M ≤ 16*(∑ i, (clean i).length) ∧ (∑ i, (clean i).length) ≤ M ∧ frozenListCaps n p M clean := by
  let cuts := partitionListPaths paths part
  have cutSimple (i : I ×ₗ B) : (cuts i).Nodup :=
    (partitionListPath_sublist paths part i).nodup (simple _)
  have cap (i : I ×ₗ B) : (cuts i).length ≤ 4*M/p := by
    have same : (cuts i).toFinset = ((paths (ofLex i).1).toFinset.filter (fun x => part x = (ofLex i).2)) := by
      ext x
      simp only [mem_filter, List.mem_toFinset]
      exact partitionListPath_mem
    rw [← List.toFinset_card_of_nodup (cutSimple i), same]
    exact lengthCap _ _
  have mass : (∑ i, (cuts i).length) = ∑ i, (paths i).length :=
    partitionListPaths_mass paths part simple
  have degrees : (half = true → k ≤ 4) ∨
      (∀ v, (occurrences (fun i => (cuts i).toFinset) v).card ≤ 4*M/n) :=
    degreeCondition.imp_right (fun bound v => (partitionListPaths_degree paths part v).le.trans (bound v))
  exact regularization_list_frozen_after_length_cap cuts cutSimple
    (partitionListPaths_admissible paths part simple allowed) hn hp dense long vertices
    (by simpa only [Fintype.card_lex, Fintype.card_prod] using pieces) cap degrees
    (by rw [mass]; exact loss) (by rw [mass]; exact massCap)

/-- Partition at most `n` vertices into groups of capacity `⌊4M/p⌋`.
This handles a subfamily carrying three quarters of the mass whenever
the original path budget has room for one copy per path and group. -/
theorem regularization_list_frozen_subfamily_in_blocks [Fintype I]
    [Fintype V] {half : Bool} {k n p M : ℕ}
    (paths : I → List V) (simple : ∀ i, (paths i).Nodup)
    (allowed : localOrderAdmissible half k paths)
    (degreeCondition : (half = true → k ≤ 4) ∨
      (∀ v, (occurrences (fun i => (paths i).toFinset) v).card ≤ 4*M/n))
    (hn : 0 < n) (hp : 0 < p) (dense : n ≤ M) (long : p ≤ M)
    (vertices : Fintype.card V ≤ n)
    (room : Fintype.card I * ((n + 4*M/p - 1) / (4*M/p)) ≤ p)
    (loss : 3*M ≤ 4*(∑ i, (paths i).length)) (massCap : (∑ i, (paths i).length) ≤ M) :
    ∃ n' ≤ n, ∃ p' ≤ p, ∃ clean : Fin p' → List (Fin n'),
      (∀ i, (clean i).Nodup) ∧ localOrderAdmissible half k clean ∧
      M ≤ 16*(∑ i, (clean i).length) ∧ (∑ i, (clean i).length) ≤ M ∧ frozenListCaps n p M clean := by
  let width := 4*M/p
  let groups := (n+width-1)/width
  have widthPos : 0 < width := (four_average_width hp long).1
  have cover : n ≤ groups*width := by
    have rounded := Nat.lt_mul_div_succ (n+width-1) widthPos
    change n+width-1 < width*(groups+1) at rounded
    rw [Nat.mul_succ, mul_comm width groups] at rounded
    omega
  let position : V ↪ Fin groups × Fin width := (Fintype.equivFin V).toEmbedding.trans
    ((Fin.castLEEmb (vertices.trans cover)).trans finProdFinEquiv.symm.toEmbedding)
  let part (v : V) := (position v).1
  have cap (i : I) (b : Fin groups) : ((paths i).toFinset.filter (fun x => part x = b)).card ≤ width := by
    have injective : Set.InjOn (fun v => (position v).2) (↑((paths i).toFinset.filter (fun x => part x = b)) : Set V) := by
      intro x hx y hy same
      apply position.injective
      exact Prod.ext ((mem_filter.mp (Finset.mem_coe.mp hx)).2.trans
        (mem_filter.mp (Finset.mem_coe.mp hy)).2.symm) same
    have card := card_le_card_of_injOn (fun v => (position v).2)
      (fun _ _ => mem_univ _) injective
    simpa only [card_univ, Fintype.card_fin] using card
  exact regularization_list_frozen_by_vertex_partition paths part simple allowed degreeCondition hn hp dense long
    vertices (by simpa only [Fintype.card_fin, groups, width] using room) cap loss massCap

end OnlineReachabilityPreservers
