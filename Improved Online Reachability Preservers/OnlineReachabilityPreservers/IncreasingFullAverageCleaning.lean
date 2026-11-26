import OnlineReachabilityPreservers.FrozenBoundaryCases

/-! Output-average cleaning from common orders and full precedence components. -/

namespace OnlineReachabilityPreservers

open Finset
open scoped Sigma.Lex

local notation "Before" => SourceAudit.BeforeIn

private theorem before_iff_of_increasing {I V : Type*} [LinearOrder V] {paths : I → List V}
    (ordered : ∀ {i x y}, Before paths i x y → x < y) (i : I) (x y : V) :
    Before paths i x y ↔ PathBefore (fun j => (paths j).toFinset) i x y := by
  constructor
  · intro step
    exact ⟨List.mem_toFinset.mpr step.1,List.mem_toFinset.mpr step.2.1,ordered step⟩
  · intro step
    have onX := List.mem_toFinset.mp step.1
    have onY := List.mem_toFinset.mp step.2.1
    have different : (paths i).idxOf x ≠ (paths i).idxOf y := fun equal =>
      step.2.2.ne ((List.idxOf_inj onX).mp equal)
    rcases lt_or_gt_of_ne different with forward | backward
    · exact ⟨onX,onY,forward⟩
    · exact (step.2.2.not_gt (ordered (i := i) ⟨onY,onX,backward⟩)).elim

/-- For ordered lists, the width split agrees with a convex set split in
the common vertex order. It preserves full exclusion at every cutoff. -/
theorem listRegularizedPaths_fullFree_of_increasing {I V : Type*}
    [LinearOrder I] [Fintype I] [LinearOrder V] {paths : I → List V} {k : ℕ}
    (simple : ∀ i, (paths i).Nodup) (free : BridgeFree (Before paths) k)
    (ordered : ∀ {i x y}, Before paths i x y → x < y) (D L : ℕ) :
    BridgeFree (Before (listRegularizedPaths paths D L)) k := by
  let copies := splitListVertices paths D
  let pieces := splitListPaths copies L
  let mark (i : I) := (copies i).toFinset
  let pieceMark (i : ListBlockIndex copies L) := (pieces i).toFinset
  have copySimple (i : I) : (copies i).Nodup := splitListVertices_simple paths D i (simple i)
  have copyStep {i x y} (step : Before copies i x y) : Before paths i x.fst y.fst :=
    splitListVertices_step (simple i) step
  have copyOrder {i x y} (step : Before copies i x y) : x < y :=
    Sigma.Lex.left _ _ (ordered (copyStep step))
  have pieceStep {i x y} (step : Before pieces i x y) : Before copies i.fst x y :=
    listBefore_of_sublist (paths := fun j : ListBlockIndex copies L => copies j.fst)
      (cut := pieces) (copySimple i.fst) List.filter_sublist step
  have pieceOrder {i x y} (step : Before pieces i x y) : x < y := copyOrder (pieceStep step)
  have copyFree : BridgeFree (Before copies) k :=
    free.split_list_vertices_any (·.fst) (fun {_ _ _} => copyStep)
  have setFree : BridgeFree (PathBefore mark) k := by
    intro s small
    exact ⟨fun b => (copyFree small).false
      (b.mapPaths id Function.injective_id (fun i x y => (before_iff_of_increasing (fun {_ _ _} => copyOrder) i x y).mpr))⟩
  have setPieces : BridgeFree (PathBefore pieceMark) k := by
    apply setFree.split_paths (fun i => i.fst)
    · intro j x here
      exact List.mem_toFinset.mpr (mem_localPathBlock.mp (List.mem_toFinset.mp here)).1
    · intro i j different same
      exact disjoint_left.mpr fun x first second =>
        splitListPaths_disjoint different same (List.mem_toFinset.mp first) (List.mem_toFinset.mp second)
    · intro j x y z left right middle low high
      have outsideX : x ∈ copies j.fst := (mem_localPathBlock.mp (List.mem_toFinset.mp left)).1
      have outsideZ : z ∈ copies j.fst := (mem_localPathBlock.mp (List.mem_toFinset.mp right)).1
      have outsideY : y ∈ copies j.fst := List.mem_toFinset.mp middle
      have rankMono {u v} (uOn : u ∈ copies j.fst) (vOn : v ∈ copies j.fst) (le : u ≤ v) :
          (copies j.fst).idxOf u ≤ (copies j.fst).idxOf v := by
        rcases lt_or_eq_of_le le with lt | eq
        · exact ((before_iff_of_increasing (fun {_ _ _} => copyOrder) j.fst u v).mpr
            ⟨List.mem_toFinset.mpr uOn,List.mem_toFinset.mpr vOn,lt⟩).2.2.le
        · exact eq ▸ le_rfl
      have lowQ : (copies j.fst).idxOf x/L ≤ (copies j.fst).idxOf y/L :=
        Nat.div_le_div_right (rankMono outsideX outsideY low)
      have highQ : (copies j.fst).idxOf y/L ≤ (copies j.fst).idxOf z/L :=
        Nat.div_le_div_right (rankMono outsideY outsideZ high)
      have xBlock : (copies j.fst).idxOf x/L = j.snd.val :=
        (mem_localPathBlock.mp (List.mem_toFinset.mp left)).2
      have zBlock : (copies j.fst).idxOf z/L = j.snd.val :=
        (mem_localPathBlock.mp (List.mem_toFinset.mp right)).2
      exact List.mem_toFinset.mpr (mem_localPathBlock.mpr
        ⟨outsideY,le_antisymm (highQ.trans zBlock.le) (xBlock.symm.le.trans lowQ)⟩)
  intro s small
  exact ⟨fun b => (setPieces small).false
    (b.mapPaths id Function.injective_id (fun j x y => (before_iff_of_increasing (fun {_ _ _} => pieceOrder) j x y).mp))⟩

/-- In the dense case, the componentwise increasing subsequence construction
gives a constant-mass witness measured against its own averages. -/
private theorem regularization_list_output_average_full_dense_of_component_fullFree {n p k : ℕ}
    (paths : Fin p → List (Fin n)) (simple : ∀ i, (paths i).Nodup)
    (free : BridgeFree (Before paths) k)
    (localFree : ∀ c d, IsEmpty (Bridge (Before (pathsInPrecedenceComponent paths c)) d))
    (three : 3 ≤ k) (hn : 0 < n) (hp : 0 < p)
    (large : 8*max n p < ∑ i, (paths i).length) :
    let M := ∑ i, (paths i).length
    ∃ n' ≤ n, ∃ p' ≤ p, ∃ clean : Fin p' → List (Fin n'),
      (∀ i, (clean i).Nodup) ∧ BridgeFree (Before clean) k ∧
      M ≤ 523*(∑ i, (clean i).length) ∧ (∑ i, (clean i).length) ≤ M ∧ listOutputAverageCaps clean := by
  let M := ∑ i, (paths i).length
  obtain ⟨rank,kept,sub,increasing,_,_,deleted⟩ :=
    fullBridgeFree_increasing_subsequences_two_of_components paths simple localFree
  let rows (i : Fin p) := (kept i).map rank
  let K := ∑ i, (rows i).length
  have keptSimple (i : Fin p) : (kept i).Nodup := (sub i).nodup (simple i)
  have rowSimple (i : Fin p) : (rows i).Nodup := (keptSimple i).map rank.injective
  have back : (fun i => (rows i).map rank.symm) = kept := by
    funext i
    simp [rows,List.map_map,Function.comp_def]
  have stepBack {i x y} (step : Before rows i x y) : Before kept i (rank.symm x) (rank.symm y) := by
    have simpleBack : ((rows i).map rank.symm).Nodup := by rw [congrFun back i]; exact keptSimple i
    have projected := listBefore_map rank.symm simpleBack step
    rw [back] at projected
    exact projected
  have keptFree : BridgeFree (Before kept) k := by
    intro size small
    exact ⟨fun bridge => (free small).false (bridge.mapPaths id Function.injective_id
      (fun i _ _ step => listBefore_of_sublist (simple i) (sub i) step))⟩
  have rowsFree : BridgeFree (Before rows) k := by
    intro size small
    exact ⟨fun bridge => (keptFree small).false
      (bridge.mapVertices rank.symm rank.symm.injective (fun _ _ _ step => stepBack step))⟩
  have stepOrder {i x y} (step : Before rows i x y) : x < y := by
    let a : Fin (rows i).length := ⟨(rows i).idxOf x,List.idxOf_lt_length_of_mem step.1⟩
    let b : Fin (rows i).length := ⟨(rows i).idxOf y,List.idxOf_lt_length_of_mem step.2.1⟩
    have comparison := (increasing i).rel_get_of_lt (a := a) (b := b) (show a < b from step.2.2)
    change (rows i)[(rows i).idxOf x]'a.isLt < (rows i)[(rows i).idxOf y]'b.isLt at comparison
    rwa [List.getElem_idxOf,List.getElem_idxOf] at comparison
  have restrictedSafe : ∀ (A : Finset (Fin n)) (B : Finset (Fin p)) (D L : ℕ),
      let quarter := restrictListPaths (removeOppositeIntersections rows) A B
      (∀ i, (quarter i).Nodup) →
      (∀ {a b x y}, a ≠ b → x ∈ quarter a → x ∈ quarter b → y ∈ quarter a → y ∈ quarter b → x = y) →
      BridgeFree (Before quarter) k →
      BridgeFree (Before (listRegularizedPaths quarter D L)) k := by
    intro A B D L
    dsimp only
    intro simpleQuarter _ freeQuarter
    apply listRegularizedPaths_fullFree_of_increasing simpleQuarter freeQuarter
    intro i x y step
    have prunedSub := removeOppositeIntersections_sublist rows i.val
    have parent := restrictListPaths_step (prunedSub.nodup (rowSimple i.val)) step
    exact stepOrder (listBefore_of_sublist (rowSimple i.val) prunedSub parent)
  have massRows : K = ∑ i, (kept i).length := by simp [K,rows]
  have massUpper : K ≤ M := by rw [massRows]; exact sum_le_sum fun i _ => (sub i).length_le
  have paid : M ≤ K+2*n := by rw [massRows]; exact deleted
  have vBound : 8*n < M := (Nat.mul_le_mul_left _ (le_max_left _ _)).trans_lt large
  have pBound : 8*p < M := (Nat.mul_le_mul_left _ (le_max_right _ _)).trans_lt large
  have dense : n ≤ K := by omega
  have long : p ≤ K := by omega
  obtain ⟨v,vFits,q,qFits,clean,cleanSimple,cleanFree,retained,upper,caps⟩ :=
    regularization_list_output_average_of_pruned_rectangle_splits rows rowSimple false rowsFree
      three restrictedSafe hn hp dense long
  change K ≤ 392*(∑ i, (clean i).length) at retained
  have lower : 3*M ≤ 4*K := by omega
  exact ⟨v,vFits,q,qFits,clean,cleanSimple,cleanFree,by omega,upper.trans massUpper,caps⟩

/-- If each precedence component excludes full bridges at every size,
retain at least one 523rd of the original mass with output-average caps. -/
theorem regularization_list_output_average_full_of_component_fullFree {n p k : ℕ}
    (paths : Fin p → List (Fin n)) (simple : ∀ i, (paths i).Nodup)
    (free : BridgeFree (Before paths) k)
    (localFree : ∀ c d, IsEmpty (Bridge (Before (pathsInPrecedenceComponent paths c)) d))
    (three : 3 ≤ k) (hn : 0 < n) (hp : 0 < p)
    (dense : n ≤ ∑ i, (paths i).length) (long : p ≤ ∑ i, (paths i).length) :
    let M := ∑ i, (paths i).length
    ∃ n' ≤ n, ∃ p' ≤ p, ∃ clean : Fin p' → List (Fin n'),
      (∀ i, (clean i).Nodup) ∧ BridgeFree (Before clean) k ∧
      M ≤ 523*(∑ i, (clean i).length) ∧ (∑ i, (clean i).length) ≤ M ∧ listOutputAverageCaps clean := by
  let M := ∑ i, (paths i).length
  by_cases small : M ≤ 8*max n p
  · obtain ⟨v,vBudget,q,qBudget,clean,cleanSimple,cleanFree,mass,upper,caps⟩ :=
      regularization_list_output_average_of_linear_mass (k := k) false hn hp dense long (by omega)
    exact ⟨v,vBudget,q,qBudget,clean,cleanSimple,cleanFree,
      mass.trans (Nat.mul_le_mul_right _ (by decide)),upper,caps⟩
  exact regularization_list_output_average_full_dense_of_component_fullFree paths simple free localFree
    three hn hp (Nat.lt_of_not_ge small)

/-- All-size full exclusion admits a cleaning witness within both original
budgets, retaining at least one 523rd of the original mass. -/
theorem regularization_list_output_average_full_all {n p : ℕ}
    (paths : Fin p → List (Fin n)) (simple : ∀ i, (paths i).Nodup)
    (free : ∀ d, IsEmpty (Bridge (Before paths) d))
    (hn : 0 < n) (hp : 0 < p) (dense : n ≤ ∑ i, (paths i).length) (long : p ≤ ∑ i, (paths i).length) :
    let M := ∑ i, (paths i).length
    ∃ n' ≤ n, ∃ p' ≤ p, ∃ clean : Fin p' → List (Fin n'),
      (∀ i, (clean i).Nodup) ∧ (∀ d, IsEmpty (Bridge (Before clean) d)) ∧
      M ≤ 523*(∑ i, (clean i).length) ∧ (∑ i, (clean i).length) ≤ M ∧ listOutputAverageCaps clean := by
  let cutoff := max 3 p
  have full : BridgeFree (Before paths) cutoff := fun d _ => free d
  obtain ⟨v,vBudget,q,qBudget,clean,cleanSimple,cleanFree,mass,upper,caps⟩ :=
    regularization_list_output_average_full_of_component_fullFree paths simple full
      (precedenceComponent_fullFree simple free) (le_max_left _ _) hn hp dense long
  exact ⟨v,vBudget,q,qBudget,clean,cleanSimple,bridgeFree_all_of_cutoff_ge_min cleanFree
    ((min_le_right _ _).trans (qBudget.trans (le_max_right _ _))),mass,upper,caps⟩

/-- A full cutoff at least the smaller budget admits output-average
cleaning of the unrestricted maximum at positive budgets. -/
theorem localOrderExtremal_output_average_full_of_cutoff_ge_min (n p k : ℕ)
    (hn : 0 < n) (hp : 0 < p) (large : min n p ≤ k) :
    ∃ paths : Fin p → List (Fin n), (∀ i, (paths i).Nodup) ∧ BridgeFree (Before paths) k ∧
      (∀ other : Fin p → List (Fin n), (∀ i, (other i).Nodup) → BridgeFree (Before other) k →
        (∑ i, (other i).length) ≤ ∑ i, (paths i).length) ∧
      let M := ∑ i, (paths i).length
      ∃ n' ≤ n, ∃ p' ≤ p, ∃ clean : Fin p' → List (Fin n'),
        (∀ i, (clean i).Nodup) ∧ (∀ d, IsEmpty (Bridge (Before clean) d)) ∧
        M ≤ 523*(∑ i, (clean i).length) ∧ (∑ i, (clean i).length) ≤ M ∧ listOutputAverageCaps clean := by
  obtain ⟨paths,simple,free,maximal,dense,long⟩ := localOrderExtremal_isDense n p k false hn hp
  exact ⟨paths,simple,free,maximal,
    regularization_list_output_average_full_all paths simple (bridgeFree_all_of_cutoff_ge_min free large)
      hn hp dense long⟩

end OnlineReachabilityPreservers
