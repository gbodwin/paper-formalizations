import OnlineReachabilityPreservers.LocalOrderExtremal

/-! The literal set and sequence readings of the path-system definition. -/

namespace OnlineReachabilityPreservers

open Finset

local notation "ListBefore" => SourceAudit.BeforeIn

private theorem firstTwo_before {n p : ℕ} {paths : Fin p → List (Fin n)} {i : Fin p}
    (simple : (paths i).Nodup) (long : 2 ≤ (paths i).length) :
    ListBefore paths i ((paths i)[0]'(by omega)) ((paths i)[1]'(by omega)) := by
  refine ⟨List.getElem_mem _,List.getElem_mem _,?_⟩
  simpa only [simple.idxOf_getElem] using (show (0 : ℕ) < 1 by decide)

/-- Any set of distinct nonempty simple paths with no half bridges of size
at most three has fewer than `n²` paths when `n ≥ 3`. -/
theorem distinctPathCount_lt_square {n p : ℕ} (hn : 3 ≤ n)
    (paths : Fin p → List (Fin n)) (distinct : Function.Injective paths)
    (nonempty : ∀ i, paths i ≠ []) (simple : ∀ i, (paths i).Nodup)
    (free : HalfBridgeFree (ListBefore paths) 3) : p < n^2 := by
  classical
  let long := (univ : Finset (Fin p)).filter fun i => 2 ≤ (paths i).length
  let short := (univ : Finset (Fin p)) \ long
  have count : short.card+long.card = p := by
    simpa only [card_univ, Fintype.card_fin] using card_sdiff_add_card_eq_card (subset_univ long)
  let head (i : short) := (paths i).head (nonempty i)
  have singleton (i : short) : paths i = [head i] := by
    have length : ¬2 ≤ (paths i).length := fun bound =>
      (mem_sdiff.mp i.property).2 (mem_filter.mpr ⟨mem_univ _,bound⟩)
    cases row : paths i with
    | nil => exact (nonempty i row).elim
    | cons x rest =>
      cases rest with
      | nil => simp only [head, List.head_eq_getElem, row, List.getElem_cons_zero]
      | cons y tail => simp [row] at length
  have shortBound : short.card ≤ n := by
    have injective : Function.Injective head := by
      intro i j eq
      apply Subtype.ext (distinct ?_)
      rw [singleton i, singleton j, eq]
    simpa only [Fintype.card_coe, Fintype.card_fin] using Fintype.card_le_of_injective head injective
  have longEnough (i : long) : 2 ≤ (paths i).length := (mem_filter.mp i.property).2
  let first (i : long) : Fin n × Fin n :=
    ((paths i)[0]'(by have := longEnough i; omega), (paths i)[1]'(by have := longEnough i; omega))
  have step (i : long) : ListBefore paths i (first i).1 (first i).2 := by
    exact firstTwo_before (simple i) (longEnough i)
  have firstInjective : Function.Injective first := by
    intro i j eq
    by_contra different
    exact no_parallel_list_steps free (by decide) (fun h => different (Subtype.ext h))
      (step i) (eq ▸ step j)
  let entries := (univ : Finset long).image first
  let off := (univ : Finset (Fin n)).offDiag
  have sub : entries ⊆ off := by
    rintro pair inside
    obtain ⟨i,_,rfl⟩ := mem_image.mp inside
    simp [off, listBefore_ne (step i)]
  have proper : entries ≠ off := by
    intro same
    let x : Fin n := ⟨0,by omega⟩
    let y : Fin n := ⟨1,by omega⟩
    let z : Fin n := ⟨2,by omega⟩
    have xy : x ≠ y := by simp [x,y,Fin.ext_iff]
    have yz : y ≠ z := by simp [y,z,Fin.ext_iff]
    have xz : x ≠ z := by simp [x,z,Fin.ext_iff]
    have find {u v : Fin n} (diff : u ≠ v) : ∃ i : long, first i = (u,v) := by
      have member : (u,v) ∈ entries := by rw [same]; simp [off,diff]
      obtain ⟨i,_,eq⟩ := mem_image.mp member
      exact ⟨i,eq⟩
    obtain ⟨a,ab⟩ := find xy
    obtain ⟨b,ba⟩ := find xy.symm
    obtain ⟨c,az⟩ := find xz
    obtain ⟨d,bz⟩ := find yz
    have separate {i j : long} {u v s t : Fin n} (left : first i = (u,v))
        (right : first j = (s,t)) (diff : (u,v) ≠ (s,t)) : (i : Fin p) ≠ j := by
      intro eq
      exact diff (left.symm.trans ((congrArg first (Subtype.ext eq)).trans right))
    have order : (c : Fin p) ≠ d := separate az bz (fun eq => xy (congrArg Prod.fst eq))
    have firstStep : ListBefore paths a x y := by simpa only [ab] using step a
    have backStep : ListBefore paths b y x := by simpa only [ba] using step b
    have leftStep : ListBefore paths c x z := by simpa only [az] using step c
    have rightStep : ListBefore paths d y z := by simpa only [bz] using step d
    rcases lt_or_gt_of_ne order with earlier | later
    · exact free (by decide) (threeListBridge
        (separate ba az (fun eq => xy.symm (congrArg Prod.fst eq)))
        (separate bz ba (fun eq => xz.symm (congrArg Prod.snd eq))) order.symm
        backStep leftStep rightStep) earlier
    · exact free (by decide) (threeListBridge
        (separate ab bz (fun eq => xy (congrArg Prod.fst eq)))
        (separate az ab (fun eq => yz.symm (congrArg Prod.snd eq))) order
        firstStep rightStep leftStep) later
  have less := card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨sub,proper⟩)
  have size : entries.card = long.card := by
    simp only [entries, card_image_of_injective _ firstInjective, card_univ, Fintype.card_coe]
  rw [size] at less
  simp only [off, offDiag_card, card_univ, Fintype.card_fin] at less
  have nBound : n ≤ n*n := by
    simpa only [mul_one] using Nat.mul_le_mul_left n (show 1 ≤ n by omega)
  rw [pow_two]
  omega

/-- The indexed convention retains all nontrivial paths in a literal set
of at most the original path budget. Removing only shorter rows loses at
most one incidence per original path and preserves either bridge exclusion. -/
theorem distinctPaths_within_budget {n p k : ℕ} (two : 2 ≤ k) (half : Bool)
    (paths : Fin p → List (Fin n)) (simple : ∀ i, (paths i).Nodup)
    (free : localOrderAdmissible half k paths) :
    ∃ q ≤ p, ∃ kept : Fin q → List (Fin n), Function.Injective kept ∧
      (∀ i, (kept i).Nodup ∧ 2 ≤ (kept i).length) ∧ localOrderAdmissible half k kept ∧
      (∑ i, (paths i).length) ≤ (∑ i, (kept i).length)+p := by
  classical
  let long := (univ : Finset (Fin p)).filter fun i => 2 ≤ (paths i).length
  let order : Fin long.card ≃o long := Fintype.orderIsoFinOfCardEq long (Fintype.card_coe long)
  let label (i : Fin long.card) : Fin p := (order i).val
  let kept (i : Fin long.card) : List (Fin n) := paths (label i)
  have arrives : StrictMono label := fun _ _ earlier => order.strictMono earlier
  have length (i : Fin long.card) : 2 ≤ (kept i).length := (mem_filter.mp (order i).property).2
  have step {i x y} (h : ListBefore kept i x y) : ListBefore paths (label i) x y := h
  have sameStep {i j : Fin long.card} (eq : kept i = kept j) {x y : Fin n}
      (h : ListBefore kept i x y) : ListBefore kept j x y := by
    unfold SourceAudit.BeforeIn at h ⊢
    rw [← eq]
    exact h
  refine ⟨long.card,by simpa only [card_univ, Fintype.card_fin] using card_le_univ long,kept,?_,
    fun i => ⟨simple (label i),length i⟩,?_,?_⟩
  · intro i j equal
    by_contra different
    have one : ListBefore kept i ((kept i)[0]'(by have := length i; omega))
        ((kept i)[1]'(by have := length i; omega)) := firstTwo_before (simple (label i)) (length i)
    have noHalf : HalfBridgeFree (ListBefore paths) k := by
      cases half
      · exact (show BridgeFree (ListBefore paths) k from free).halfFree
      · exact free
    exact no_parallel_list_steps noHalf two (fun eq => different (arrives.injective eq))
      (step one) (step (sameStep equal one))
  · cases half
    · intro m bound
      exact ⟨fun b => (free bound).false (b.mapPaths label arrives.injective (fun _ _ _ h => step h))⟩
    · intro m bound b earlier
      exact free bound (b.mapPaths label arrives.injective (fun _ _ _ h => step h)) (arrives earlier)
  · have keptMass : (∑ i, (kept i).length) = ∑ i ∈ long, (paths i).length :=
      (Equiv.sum_comp order.toEquiv (fun i : long => (paths i).length)).trans
        (long.sum_coe_sort (fun i => (paths i).length))
    have remainder : (∑ i ∈ longᶜ, (paths i).length) ≤ p := by
      calc
        _ ≤ ∑ _i ∈ longᶜ, 1 := sum_le_sum fun i hi => by
          have outside : i ∉ long := mem_compl.mp hi
          have short : ¬ 2 ≤ (paths i).length := fun bound => outside (mem_filter.mpr ⟨mem_univ _,bound⟩)
          omega
        _ = (longᶜ : Finset (Fin p)).card := by simp
        _ ≤ p := by simpa only [card_univ, Fintype.card_fin] using card_le_univ (longᶜ : Finset (Fin p))
    rw [keptMass, ← sum_add_sum_compl long (fun i => (paths i).length)]
    exact Nat.add_le_add_left remainder _

/-- If repeated vertices are permitted, distinct nonempty sequences have
unbounded incidence mass even under exclusion of all full bridges. -/
theorem distinctSequenceMass_unbounded {n p : ℕ} (hn : 0 < n) (hp : 0 < p) (M : ℕ) :
    ∃ paths : Fin p → List (Fin n), Function.Injective paths ∧ (∀ i, paths i ≠ []) ∧
      (∀ k, IsEmpty (Bridge (ListBefore paths) k)) ∧ M < ∑ i, (paths i).length := by
  let paths (i : Fin p) : List (Fin n) := List.replicate (M+i.val+1) ⟨0,hn⟩
  refine ⟨paths, ?_, ?_, ?_, ?_⟩
  · intro i j eq
    have length := congrArg List.length eq
    simp only [paths, List.length_replicate] at length
    exact Fin.ext (by omega)
  · intro i empty
    have length := congrArg List.length empty
    simp [paths] at length
  · intro k
    refine ⟨fun b => listBefore_ne b.riverStep ?_⟩
    exact (List.eq_of_mem_replicate b.riverStep.1).trans (List.eq_of_mem_replicate b.riverStep.2.1).symm
  · have kept := single_le_sum (f := fun i : Fin p => (paths i).length)
      (fun i _ => Nat.zero_le _) (a := (⟨0,hp⟩ : Fin p)) (mem_univ _)
    simp only [paths, List.length_replicate, Nat.add_zero] at kept ⊢
    omega

end OnlineReachabilityPreservers
