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

/-- Half-two exclusion prevents duplicated simple rows of length at least two. -/
theorem nontrivial_halfFree_paths_injective {n p k : ℕ} {paths : Fin p → List (Fin n)}
    (simple : ∀ i, (paths i).Nodup) (length : ∀ i, 2 ≤ (paths i).length)
    (two : 2 ≤ k) (free : HalfBridgeFree (ListBefore paths) k) : Function.Injective paths := by
  intro i j eq
  by_contra different
  have step := firstTwo_before (simple i) (length i)
  have parallel : ListBefore paths j ((paths i)[0]'(by have := length i; omega))
      ((paths i)[1]'(by have := length i; omega)) := by
    unfold SourceAudit.BeforeIn at *
    rw [← eq]
    exact step
  exact no_parallel_list_steps free two different step parallel

/-- Encoding singleton rows on the diagonal and longer rows by their
first pair gives at most n squared paths in the literal simple-path set model. -/
theorem distinctPathCount_le_square {n p k : ℕ} (paths : Fin p → List (Fin n))
    (distinct : Function.Injective paths) (nonempty : ∀ i, paths i ≠ [])
    (simple : ∀ i, (paths i).Nodup) (two : 2 ≤ k)
    (free : HalfBridgeFree (ListBefore paths) k) : p ≤ n^2 := by
  let head (i : Fin p) : Fin n := (paths i)[0]'(List.length_pos_of_ne_nil (nonempty i))
  let second (i : Fin p) : Fin n :=
    if h : 2 ≤ (paths i).length then (paths i)[1]'(by omega) else head i
  let code (i : Fin p) : Fin n × Fin n := (head i,second i)
  have step (i : Fin p) (long : 2 ≤ (paths i).length) : ListBefore paths i (head i) (second i) := by
    simpa only [head,second,dite_eq_left long] using firstTwo_before (simple i) long
  have same (i : Fin p) (short : ¬2 ≤ (paths i).length) : second i = head i := dite_eq_right short
  have single (i : Fin p) (short : ¬2 ≤ (paths i).length) : paths i = [head i] := by
    revert short
    generalize eq : paths i = row at *
    cases row with
    | nil => exact (nonempty i eq).elim
    | cons a rest =>
      cases rest with
      | nil => simp [head,eq]
      | cons b rest => simp
  have injection : Function.Injective code := by
    intro i j eq
    have firstEq : head i = head j := congrArg Prod.fst eq
    have secondEq : second i = second j := congrArg Prod.snd eq
    by_cases longI : 2 ≤ (paths i).length <;> by_cases longJ : 2 ≤ (paths j).length
    · by_contra different
      exact no_parallel_list_steps free two different (step i longI)
        (firstEq.symm ▸ secondEq.symm ▸ step j longJ)
    · exact (listBefore_ne (step i longI) (firstEq.trans ((same j longJ).symm.trans secondEq.symm))).elim
    · exact (listBefore_ne (step j longJ) (firstEq.symm.trans ((same i longI).symm.trans secondEq))).elim
    · apply distinct
      rw [single i longI,single j longJ,firstEq]
  simpa [pow_two] using Fintype.card_le_of_injective code injection

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

/-- Every corner of a bridge occurs on two distinct paths. -/
theorem bridgeCorner_twoPaths {V I : Type*} [DecidableEq V]
    {paths : I → List V} {k : ℕ} (b : Bridge (ListBefore paths) k) (j : Fin (k+2)) :
    ∃ a c, a ≠ c ∧ b.vertex j ∈ paths a ∧ b.vertex j ∈ paths c := by
  refine Fin.cases ?_ ?_ j
  · exact ⟨b.river,b.arc 0,b.river_ne_arc 0,b.riverStep.1,(b.arcStep 0).1⟩
  · intro i
    refine Fin.lastCases (motive := fun i : Fin (k+1) =>
      ∃ a c, a ≠ c ∧ b.vertex i.succ ∈ paths a ∧ b.vertex i.succ ∈ paths c) ?_ ?_ i
    · rw [Fin.succ_last]
      exact ⟨b.river,b.arc (Fin.last k),b.river_ne_arc _,b.riverStep.2.1,(b.arcStep _).2.1⟩
    · intro h
      have apart : h.castSucc ≠ h.succ := by
        intro eq
        have value := congrArg Fin.val eq
        simp only [Fin.val_castSucc,Fin.val_succ] at value
        omega
      refine ⟨b.arc h.castSucc,b.arc h.succ,fun eq => apart (b.distinctArcs eq),
        (b.arcStep h.castSucc).2.1,?_⟩
      rw [Fin.succ_castSucc]
      exact (b.arcStep h.succ).1

private def appendUnusedVertex {n p : ℕ} (paths : Fin p → List (Fin n)) (row : Fin p)
    (v : Fin n) (i : Fin p) : List (Fin n) :=
  if i = row then paths i ++ [v] else paths i

private theorem appendUnusedVertex_admissible {n p k : ℕ} {half : Bool}
    (paths : Fin p → List (Fin n)) (row : Fin p) (v : Fin n) (unused : ∀ i, v ∉ paths i)
    (free : localOrderAdmissible half k paths) :
    localOrderAdmissible half k (appendUnusedVertex paths row v) := by
  let extended := appendUnusedVertex paths row v
  have unique {i : Fin p} (present : v ∈ extended i) : i = row := by
    by_contra outside
    exact unused i (by simpa [extended,appendUnusedVertex,outside] using present)
  have projectStep {i : Fin p} {x y : Fin n} (differentX : x ≠ v) (differentY : y ≠ v)
      (step : ListBefore extended i x y) : ListBefore paths i x y := by
    by_cases changed : i = row
    · have onX : x ∈ paths i := by
        have both : x ∈ paths i ∨ x = v := by
          simpa [extended,appendUnusedVertex,changed] using step.1
        exact both.resolve_right differentX
      have onY : y ∈ paths i := by
        have both : y ∈ paths i ∨ y = v := by
          simpa [extended,appendUnusedVertex,changed] using step.2.1
        exact both.resolve_right differentY
      refine ⟨onX,onY,?_⟩
      simpa only [extended,appendUnusedVertex,ite_eq_left changed,
        List.idxOf_append_of_mem onX,List.idxOf_append_of_mem onY] using step.2.2
    · simpa only [SourceAudit.BeforeIn,extended,appendUnusedVertex,ite_eq_right changed] using step
  have project {d : ℕ} (b : Bridge (ListBefore extended) d) :
      ∃ old : Bridge (ListBefore paths) d, old.arc = b.arc ∧ old.river = b.river := by
    have away (j : Fin (d+2)) : b.vertex j ≠ v := by
      intro eq
      obtain ⟨a,c,apart,ma,mc⟩ := bridgeCorner_twoPaths b j
      exact apart ((unique (eq ▸ ma)).trans (unique (eq ▸ mc)).symm)
    let old : Bridge (ListBefore paths) d :=
      ⟨b.vertex,b.arc,b.river,b.distinctVertices,b.distinctArcs,b.river_ne_arc,
       projectStep (away _) (away _) b.riverStep,
       fun i => projectStep (away _) (away _) (b.arcStep i)⟩
    exact ⟨old,rfl,rfl⟩
  cases half
  · intro d short
    exact ⟨fun b => (free short).false (project b).choose⟩
  · intro d short b arrive
    obtain ⟨old,arc,river⟩ := project b
    apply free short old
    simpa only [arc,river] using arrive

private theorem appendUnusedVertex_distinct {n p : ℕ} (paths : Fin p → List (Fin n))
    (row : Fin p) (v : Fin n) (unused : ∀ i, v ∉ paths i) (distinct : Function.Injective paths) :
    Function.Injective (appendUnusedVertex paths row v) := by
  let extended := appendUnusedVertex paths row v
  have added : v ∈ extended row := by simp [extended,appendUnusedVertex]
  have unique {i : Fin p} (present : v ∈ extended i) : i = row := by
    by_contra outside
    exact unused i (by simpa [extended,appendUnusedVertex,outside] using present)
  intro a b same
  change extended a = extended b at same
  by_cases aEq : a = row
  · subst a
    exact (unique (same ▸ added)).symm
  · by_cases bEq : b = row
    · subst b
      exact unique (same.symm ▸ added)
    · apply distinct
      simpa only [extended,appendUnusedVertex,ite_eq_right aEq,ite_eq_right bEq] using same

private theorem appendUnusedVertex_mass {n p : ℕ} (paths : Fin p → List (Fin n))
    (row : Fin p) (v : Fin n) :
    (∑ i, (appendUnusedVertex paths row v i).length) = (∑ i, (paths i).length)+1 := by
  have length (i : Fin p) : (appendUnusedVertex paths row v i).length =
      (paths i).length + if i = row then 1 else 0 := by
    by_cases eq : i = row <;> simp [appendUnusedVertex,eq]
  simp only [length,sum_add_distrib,sum_ite_eq',mem_univ,ite_true]

/-- The literal exact-count extremum exists whenever an eligible family
exists. Its mass is at least both budgets. -/
theorem localOrderDistinctExtremal_isDense {n p k : ℕ} (half : Bool) (hp : 0 < p)
    (feasible : ∃ paths : Fin p → List (Fin n), Function.Injective paths ∧
      (∀ i, paths i ≠ [] ∧ (paths i).Nodup) ∧ localOrderAdmissible half k paths) :
    ∃ paths : Fin p → List (Fin n), Function.Injective paths ∧
      (∀ i, paths i ≠ [] ∧ (paths i).Nodup) ∧ localOrderAdmissible half k paths ∧
      (∀ other : Fin p → List (Fin n), Function.Injective other →
        (∀ i, other i ≠ [] ∧ (other i).Nodup) → localOrderAdmissible half k other →
        (∑ i, (other i).length) ≤ ∑ i, (paths i).length) ∧
      n ≤ ∑ i, (paths i).length ∧ p ≤ ∑ i, (paths i).length := by
  classical
  let Family := Fin p → {path : List (Fin n) // path.Nodup}
  let : Fintype Family := inferInstanceAs (Fintype (Fin p → {path : List (Fin n) // path.Nodup}))
  let lists (f : Family) : Fin p → List (Fin n) := fun i => (f i).val
  let choices := (univ : Finset Family).filter fun f => Function.Injective (lists f) ∧
    (∀ i, lists f i ≠ []) ∧ localOrderAdmissible half k (lists f)
  obtain ⟨available,availableDistinct,availableRows,availableFree⟩ := feasible
  let base : Family := fun i => ⟨available i,(availableRows i).2⟩
  have inside : base ∈ choices := mem_filter.mpr ⟨mem_univ _,availableDistinct,
    (fun i => (availableRows i).1),availableFree⟩
  obtain ⟨best,inChoices,maximal⟩ := exists_max_image choices (fun f => ∑ i, (lists f i).length)
    ⟨base,inside⟩
  let paths := lists best
  obtain ⟨distinct,nonempty,free⟩ := (mem_filter.mp inChoices).2
  have simple (i : Fin p) : (paths i).Nodup := (best i).property
  have maximalLists (other : Fin p → List (Fin n)) (injective : Function.Injective other)
      (rows : ∀ i, other i ≠ [] ∧ (other i).Nodup) (legal : localOrderAdmissible half k other) :
      (∑ i, (other i).length) ≤ ∑ i, (paths i).length := by
    let entry : Family := fun i => ⟨other i,(rows i).2⟩
    exact maximal entry (mem_filter.mpr ⟨mem_univ _,injective,(fun i => (rows i).1),legal⟩)
  have covers (v : Fin n) : ∃ i, v ∈ paths i := by
    by_contra! unused
    let row : Fin p := ⟨0,hp⟩
    let extended := appendUnusedVertex paths row v
    have extendedRows (i : Fin p) : extended i ≠ [] ∧ (extended i).Nodup := by
      by_cases changed : i = row
      · subst i
        have away : ∀ a ∈ paths row, a ≠ v := by
          intro a present eq
          exact unused row (eq ▸ present)
        simpa [extended,appendUnusedVertex,List.nodup_append,simple row] using away
      · simpa only [extended,appendUnusedVertex,ite_eq_right changed] using And.intro (nonempty i) (simple i)
    have extendBound := maximalLists extended (appendUnusedVertex_distinct paths row v unused distinct)
      extendedRows (appendUnusedVertex_admissible paths row v unused free)
    change (∑ i, (appendUnusedVertex paths row v i).length) ≤ ∑ i, (paths i).length at extendBound
    rw [appendUnusedVertex_mass] at extendBound
    omega
  have all : (univ : Finset (Fin p)).biUnion (fun i => (paths i).toFinset) = univ := by
    ext v
    simpa only [mem_biUnion,mem_univ,true_and,List.mem_toFinset,iff_true] using covers v
  refine ⟨paths,distinct,(fun i => ⟨nonempty i,simple i⟩),free,maximalLists,?_,?_⟩
  · calc
      n = ((univ : Finset (Fin p)).biUnion (fun i => (paths i).toFinset)).card := by simp [all]
      _ ≤ ∑ i, (paths i).toFinset.card := card_biUnion_le
      _ = _ := sum_congr rfl fun i _ => List.toFinset_card_of_nodup (simple i)
  · calc
      p = ∑ i : Fin p, (1:ℕ) := by simp
      _ ≤ _ := sum_le_sum fun i _ => List.length_pos_of_ne_nil (nonempty i)

end OnlineReachabilityPreservers
