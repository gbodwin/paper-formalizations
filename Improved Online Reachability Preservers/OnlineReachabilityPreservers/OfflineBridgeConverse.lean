import OnlineReachabilityPreservers.OfflineBridgeExtremalUpper
import OnlineReachabilityPreservers.OfflineComponentOrders
import OnlineReachabilityPreservers.OfflineConsecutiveEndpoint
import OnlineReachabilityPreservers.OfflineOrderedBlocks

/-! The converse of Lemma 14 for arbitrary local path orders. -/

namespace OnlineReachabilityPreservers

open Finset

local notation "ListBefore" => SourceAudit.BeforeIn

variable {V I : Type*} [DecidableEq V]

private theorem exists_consecutive_after {paths : I → List V} {i : I} {x y : V}
    (simple : (paths i).Nodup) (before : ListBefore paths i x y) :
    ∃ z ∈ paths i, ConsecutiveListStep paths i x z := by
  let j := (paths i).idxOf x+1
  have position : j < (paths i).length := lt_of_le_of_lt before.2.2 (List.idxOf_lt_length_of_mem before.2.1)
  let z := (paths i)[j]'position
  have onRow : z ∈ paths i := List.getElem_mem position
  have index : (paths i).idxOf z = j := simple.idxOf_getElem j position
  exact ⟨z,onRow,⟨before.1,onRow,by rw [index]; exact Nat.lt_succ_self _⟩,index.symm⟩

variable [Fintype I]

private noncomputable def laterRows (paths : I → List V) (S : Finset V) (x : V) : Finset I := by
  classical
  exact univ.filter fun i => ∃ y ∈ S, ListBefore paths i x y

private theorem mem_laterRows {paths : I → List V} {S : Finset V} {x : V} {i : I} :
    i ∈ laterRows paths S x ↔ ∃ y ∈ S, ListBefore paths i x y := by
  classical
  simp [laterRows]

private theorem exists_laterRows_le_two [Fintype V] (paths : I → List V)
    (simple : ∀ i, (paths i).Nodup) (free : ∀ d, IsEmpty (Bridge (ListBefore paths) d))
    {S : Finset V} (nonempty : S.Nonempty) : ∃ x ∈ S, (laterRows paths S x).card ≤ 2 := by
  classical
  let restricted (i : I) := (paths i).filter fun x => decide (x ∈ S)
  have sub (i : I) : (restricted i).Sublist (paths i) := List.filter_sublist
  have restrictedFree (d : ℕ) : IsEmpty (Bridge (ListBefore restricted) d) :=
    ⟨fun b => (free d).false (b.mapPaths id Function.injective_id
      (fun i _ _ step => listBefore_of_sublist (simple i) (sub i) step))⟩
  obtain ⟨x,inSet,sparse⟩ := exists_consecutiveOutgoingRows_le_two restricted restrictedFree nonempty
  refine ⟨x,inSet,(card_le_card ?_).trans sparse⟩
  intro i inRows
  obtain ⟨y,alsoInSet,step⟩ := (mem_filter.mp inRows).2
  have xOn : x ∈ restricted i := List.mem_filter.mpr ⟨step.1,decide_eq_true inSet⟩
  have yOn : y ∈ restricted i := List.mem_filter.mpr ⟨step.2.1,decide_eq_true alsoInSet⟩
  have keptStep : ListBefore restricted i x y := by
    rcases listBefore_total xOn yOn (listBefore_ne step) with ahead | back
    · exact ahead
    · exact (step.2.2.asymm (listBefore_of_sublist (simple i) (sub i) back).2.2).elim
  obtain ⟨z,onRow,next⟩ := exists_consecutive_after ((sub i).nodup (simple i)) keptStep
  exact mem_filter.mpr ⟨mem_univ _,z,of_decide_eq_true (List.mem_filter.mp onRow).2,next⟩

private noncomputable def laterLowerRows (paths : I → List V) (S : Finset V) (rank : V → ℕ) (x : V) : Finset I := by
  classical
  exact univ.filter fun i => ∃ y ∈ S, ListBefore paths i x y ∧ rank y < rank x

private theorem mem_laterLowerRows {paths : I → List V} {S : Finset V} {rank : V → ℕ} {x : V} {i : I} :
    i ∈ laterLowerRows paths S rank x ↔ ∃ y ∈ S, ListBefore paths i x y ∧ rank y < rank x := by
  classical
  simp [laterLowerRows]

private theorem exists_rank_with_few_later_lower [Fintype V] (paths : I → List V)
    (smallRows : ∀ S : Finset V, S.Nonempty → ∃ x ∈ S, (laterRows paths S x).card ≤ 2) (S : Finset V) :
    ∃ rank : V → ℕ, Set.InjOn rank (S : Set V) ∧ (∀ x ∈ S, rank x < S.card) ∧
      ∀ x ∈ S, (laterLowerRows paths S rank x).card ≤ 2 := by
  classical
  induction S using Finset.strongInduction with
  | H S previous =>
    by_cases empty : S = ∅
    · subst S
      exact ⟨fun _ => 0,by simp [Set.InjOn],by simp,by simp⟩
    obtain ⟨top,topIn,topRows⟩ := smallRows S (Finset.nonempty_iff_ne_empty.mpr empty)
    let rest := S.erase top
    obtain ⟨oldRank,oldInjective,oldRoom,oldLoss⟩ := previous rest (erase_ssubset topIn)
    let rank (x : V) := if x = top then rest.card else oldRank x
    have atTop : rank top = rest.card := ite_eq_left rfl
    have offTop {x : V} (different : x ≠ top) : rank x = oldRank x := ite_eq_right different
    have complete : insert top rest = S := insert_erase topIn
    have separate : top ∉ rest := notMem_erase _ _
    have card : S.card = rest.card+1 := by rw [← complete,card_insert_of_notMem separate]
    refine ⟨rank,?_,?_,?_⟩
    · intro x hx y hy equal
      change x ∈ S at hx
      change y ∈ S at hy
      by_cases atX : x = top <;> by_cases atY : y = top
      · exact atX.trans atY.symm
      · have room := oldRoom y (mem_erase.mpr ⟨atY,hy⟩)
        rw [atX,atTop,offTop atY] at equal
        omega
      · have room := oldRoom x (mem_erase.mpr ⟨atX,hx⟩)
        rw [atY,offTop atX,atTop] at equal
        omega
      · exact oldInjective (mem_erase.mpr ⟨atX,hx⟩) (mem_erase.mpr ⟨atY,hy⟩)
          (by simpa only [offTop atX,offTop atY] using equal)
    · intro x hx
      by_cases atX : x = top
      · rw [atX,atTop,card]
        exact Nat.lt_succ_self _
      · rw [offTop atX,card]
        exact (oldRoom x (mem_erase.mpr ⟨atX,hx⟩)).trans (Nat.lt_succ_self _)
    · have topLoss : (laterLowerRows paths S rank top).card ≤ 2 := by
        apply le_trans (card_le_card (t := laterRows paths S top) ?_) topRows
        intro i mark
        obtain ⟨y,inside,step,_⟩ := mem_laterLowerRows.mp mark
        exact mem_filter.mpr ⟨mem_univ _,y,inside,step⟩
      have remaining (x : V) (inRest : x ∈ rest) :
          (laterLowerRows paths S rank x).card ≤ (laterLowerRows paths rest oldRank x).card := by
        apply card_le_card
        intro i mark
        obtain ⟨y,yIn,step,below⟩ := mem_laterLowerRows.mp mark
        have diffX := (mem_erase.mp inRest).1
        have diffY : y ≠ top := by
          intro same
          rw [same,atTop,offTop diffX] at below
          exact below.asymm (oldRoom x inRest)
        exact mem_laterLowerRows.mpr ⟨y,mem_erase.mpr ⟨diffY,yIn⟩,step,
          by simpa only [offTop diffX,offTop diffY] using below⟩
      intro x xIn
      by_cases atX : x = top
      · simpa only [atX] using topLoss
      · have inRest : x ∈ rest := mem_erase.mpr ⟨atX,xIn⟩
        exact (remaining x inRest).trans (oldLoss x inRest)

variable {n p : ℕ}

private theorem increasing_subsequences_of_small_laterRows (paths : Fin p → List (Fin n))
    (simple : ∀ i, (paths i).Nodup)
    (smallRows : ∀ S : Finset (Fin n), S.Nonempty → ∃ x ∈ S, (laterRows paths S x).card ≤ 2) :
    ∃ rank : Fin n ≃ Fin n, ∃ kept : Fin p → List (Fin n),
      (∀ i, (kept i).Sublist (paths i)) ∧ (∀ i, ((kept i).map rank).Pairwise (· < ·)) ∧
      (∀ i (nonempty : paths i ≠ []), (paths i).getLast nonempty ∈ kept i) ∧
      (∀ x, (occurrences (fun i => (paths i).toFinset \ (kept i).toFinset) x).card ≤ 2) ∧
      (∑ i, (paths i).length) ≤ (∑ i, (kept i).length)+2*n := by
  classical
  obtain ⟨number,distinct,room,loss⟩ := exists_rank_with_few_later_lower paths smallRows univ
  let rank (x : Fin n) : Fin n := ⟨number x,by simpa using room x (mem_univ _)⟩
  have injective : Function.Injective rank :=
    fun _ _ equal => distinct (mem_univ _) (mem_univ _) (congrArg Fin.val equal)
  let order := Equiv.ofBijective rank ⟨injective,Finite.surjective_of_injective injective⟩
  let kept (i : Fin p) := (paths i).filter fun x => decide (i ∉ laterLowerRows paths univ number x)
  have sub (i : Fin p) : (kept i).Sublist (paths i) := List.filter_sublist
  have keptSimple (i : Fin p) : (kept i).Nodup := (sub i).nodup (simple i)
  have memKept {i : Fin p} {x : Fin n} : x ∈ kept i ↔ x ∈ paths i ∧ i ∉ laterLowerRows paths univ number x :=
    by simp [kept]
  refine ⟨order,kept,sub,?_,?_,?_⟩
  · intro i
    rw [List.pairwise_map,List.pairwise_iff_getElem]
    intro a b aIn bIn lt
    let x := (kept i)[a]'aIn
    let y := (kept i)[b]'bIn
    have beforeKept : ListBefore kept i x y := by
      refine ⟨List.getElem_mem aIn,List.getElem_mem bIn,?_⟩
      change (kept i).idxOf ((kept i)[a]'aIn) < (kept i).idxOf ((kept i)[b]'bIn)
      rwa [(keptSimple i).idxOf_getElem a aIn,(keptSimple i).idxOf_getElem b bIn]
    have before := listBefore_of_sublist (simple i) (sub i) beforeKept
    change rank x < rank y
    by_contra! notOrdered
    have different : rank y ≠ rank x := fun same => listBefore_ne before (injective same).symm
    have less : number y < number x := notOrdered.lt_of_ne different
    exact (memKept.mp beforeKept.1).2 (mem_laterLowerRows.mpr ⟨y,mem_univ _,before,less⟩)
  · intro i nonempty
    let last := (paths i).getLast nonempty
    refine memKept.mpr ⟨List.getLast_mem nonempty,?_⟩
    intro marked
    obtain ⟨y,_,step,_⟩ := mem_laterLowerRows.mp marked
    have lastIndex : (paths i).idxOf last = (paths i).length-1 := by
      simp only [last,List.getLast_eq_getElem,(simple i).idxOf_getElem]
    have later := step.2.2
    rw [lastIndex] at later
    have limit := List.idxOf_lt_length_of_mem step.2.1
    omega
  · let omitted (i : Fin p) := (paths i).toFinset \ (kept i).toFinset
    have counts (x : Fin n) : occurrences omitted x = laterLowerRows paths univ number x := by
      ext i
      rw [mem_occurrences]
      change x ∈ (paths i).toFinset \ (kept i).toFinset ↔ _
      simp only [mem_sdiff,List.mem_toFinset,memKept]
      refine ⟨fun present => Classical.byContradiction (fun unmarked => present.2 ⟨present.1,unmarked⟩),?_⟩
      intro mark
      obtain ⟨_,_,before,_⟩ := mem_laterLowerRows.mp mark
      exact ⟨before.1,fun retained => retained.2 mark⟩
    have localLoss (x : Fin n) : (occurrences omitted x).card ≤ 2 := by
      rw [counts]
      exact loss x (mem_univ _)
    refine ⟨localLoss,?_⟩
    have omittedMass : (∑ i, (omitted i).card) ≤ 2*n := by
      rw [← sum_occurrences omitted]
      calc
        _ ≤ ∑ _ : Fin n, 2 := sum_le_sum (fun x _ => localLoss x)
        _ = 2*n := by simp [Nat.mul_comm]
    have mass : (∑ i, (omitted i).card) + (∑ i, (kept i).length) = ∑ i, (paths i).length := by
      rw [← sum_add_distrib]
      apply sum_congr rfl
      intro i _
      have subset : (kept i).toFinset ⊆ (paths i).toFinset := fun _ member =>
        List.mem_toFinset.mpr ((sub i).subset (List.mem_toFinset.mp member))
      rw [← List.toFinset_card_of_nodup (keptSimple i),← List.toFinset_card_of_nodup (simple i)]
      exact card_sdiff_add_card_eq_card subset
    omega

/-- Delete at most two incidences per vertex to give the retained paths
one common vertex order. Every nonempty row keeps its last vertex. -/
theorem fullBridgeFree_increasing_subsequences_two (paths : Fin p → List (Fin n))
    (simple : ∀ i, (paths i).Nodup) (free : ∀ d, IsEmpty (Bridge (ListBefore paths) d)) :
    ∃ rank : Fin n ≃ Fin n, ∃ kept : Fin p → List (Fin n),
      (∀ i, (kept i).Sublist (paths i)) ∧ (∀ i, ((kept i).map rank).Pairwise (· < ·)) ∧
      (∀ i (nonempty : paths i ≠ []), (paths i).getLast nonempty ∈ kept i) ∧
      (∀ x, (occurrences (fun i => (paths i).toFinset \ (kept i).toFinset) x).card ≤ 2) ∧
      (∑ i, (paths i).length) ≤ (∑ i, (kept i).length)+2*n :=
  increasing_subsequences_of_small_laterRows paths simple
    (fun _ S => exists_laterRows_le_two paths simple free S)

/-- Whole-system bridge exclusion is enough component by component. At
each elimination, take a maximal remaining condensation component. -/
theorem fullBridgeFree_increasing_subsequences_two_of_components (paths : Fin p → List (Fin n))
    (simple : ∀ i, (paths i).Nodup)
    (localFree : ∀ c d, IsEmpty (Bridge (ListBefore (pathsInPrecedenceComponent paths c)) d)) :
    ∃ rank : Fin n ≃ Fin n, ∃ kept : Fin p → List (Fin n),
      (∀ i, (kept i).Sublist (paths i)) ∧ (∀ i, ((kept i).map rank).Pairwise (· < ·)) ∧
      (∀ i (nonempty : paths i ≠ []), (paths i).getLast nonempty ∈ kept i) ∧
      (∀ x, (occurrences (fun i => (paths i).toFinset \ (kept i).toFinset) x).card ≤ 2) ∧
      (∑ i, (paths i).length) ≤ (∑ i, (kept i).length)+2*n := by
  classical
  apply increasing_subsequences_of_small_laterRows paths simple
  intro S nonempty
  let G := pathPrecedenceGraph paths
  let label := componentLabel G
  let priority (x : Fin n) := (reaches (condensation G) (label x)).card
  obtain ⟨anchor,inSet,maximum⟩ := exists_max_image S priority nonempty
  let T := S.filter (fun x => label x = label anchor)
  let localPaths := pathsInPrecedenceComponent paths (label anchor)
  have sub (i : Fin p) : (localPaths i).Sublist (paths i) := List.filter_sublist
  have inside : T.Nonempty := ⟨anchor,mem_filter.mpr ⟨inSet,rfl⟩⟩
  obtain ⟨x,inT,small⟩ := exists_laterRows_le_two localPaths
    (fun i => (sub i).nodup (simple i)) (localFree (label anchor)) inside
  obtain ⟨inS,labelX⟩ := mem_filter.mp inT
  refine ⟨x,inS,(card_le_card ?_).trans small⟩
  intro i onRow
  obtain ⟨y,yIn,step⟩ := mem_laterRows.mp onRow
  have labelY : label y = label anchor := by
    by_contra different
    have edge : Edge G x y := mem_filter.mpr ⟨mem_univ _,i,step⟩
    have distinct : label x ≠ label y := fun same => different (same.symm.trans labelX)
    have crosses : Edge (condensation G) (label x) (label y) :=
      edge_condensation.mpr ⟨distinct,x,y,edge,rfl,rfl⟩
    have after : priority x < priority y := reaches_card_lt (condensation_dag G) crosses
    have same : priority x = priority anchor := congrArg (fun c => (reaches (condensation G) c).card) labelX
    rw [same] at after
    exact after.not_ge (maximum y yIn)
  have onX : x ∈ localPaths i := List.mem_filter.mpr ⟨step.1,decide_eq_true labelX⟩
  have onY : y ∈ localPaths i := List.mem_filter.mpr ⟨step.2.1,decide_eq_true labelY⟩
  have localStep := (listBefore_sublist_iff (simple i) (sub i) onX onY).mpr step
  exact mem_laterRows.mpr ⟨y,mem_filter.mpr ⟨yIn,labelY⟩,localStep⟩

/-- Count the original rows supplying at least one strict step inside the component. -/
noncomputable def precedenceComponentNontrivialRows (paths : Fin p → List (Fin n)) (c : Fin n) : Finset (Fin p) :=
  univ.filter fun i => 2 ≤ (pathsInPrecedenceComponent paths c i).length

/-- A strict step certifies that its original row is nontrivial in the component. -/
theorem precedenceComponent_row_mem_of_step {paths : Fin p → List (Fin n)} {c x y : Fin n} {i : Fin p}
    (step : ListBefore (pathsInPrecedenceComponent paths c) i x y) : i ∈ precedenceComponentNontrivialRows paths c := by
  refine mem_filter.mpr ⟨mem_univ _,?_⟩
  have late := List.idxOf_lt_length_of_mem step.2.1
  have before := step.2.2
  omega

/-- A local bridge uses one distinct nontrivial row per arc and for the river. -/
theorem precedenceComponent_bridge_size_le_rows {paths : Fin p → List (Fin n)} {c : Fin n} {d : ℕ}
    (bridge : Bridge (ListBefore (pathsInPrecedenceComponent paths c)) d) :
    d+2 ≤ (precedenceComponentNontrivialRows paths c).card := by
  let localPaths := pathsInPrecedenceComponent paths c
  let rows := precedenceComponentNontrivialRows paths c
  let smaller : Bridge (fun i : rows => ListBefore localPaths i.val) d :=
    { vertex := bridge.vertex
      arc := fun i => ⟨bridge.arc i,precedenceComponent_row_mem_of_step (bridge.arcStep i)⟩
      river := ⟨bridge.river,precedenceComponent_row_mem_of_step bridge.riverStep⟩
      distinctVertices := bridge.distinctVertices
      distinctArcs := fun _ _ eq => bridge.distinctArcs (congrArg Subtype.val eq)
      river_ne_arc := fun i eq => bridge.river_ne_arc i (congrArg Subtype.val eq)
      riverStep := bridge.riverStep
      arcStep := bridge.arcStep }
  simpa only [Fintype.card_coe] using SourceAudit.bridge_path_count_le smaller

/-- If each component has at most the given cutoff's worth of nontrivial
rows, the global exclusion at that cutoff excludes every bridge locally. -/
theorem precedenceComponents_fullFree_of_nontrivialRows_le {k : ℕ} (paths : Fin p → List (Fin n))
    (simple : ∀ i, (paths i).Nodup) (free : BridgeFree (ListBefore paths) k)
    (few : ∀ c, (precedenceComponentNontrivialRows paths c).card ≤ k) :
    ∀ c d, IsEmpty (Bridge (ListBefore (pathsInPrecedenceComponent paths c)) d) := by
  intro c d
  refine ⟨fun bridge => ?_⟩
  exact (free ((precedenceComponent_bridge_size_le_rows bridge).trans (few c))).false
    (bridge.mapPaths id Function.injective_id (fun i _ _ step =>
      listBefore_of_sublist (simple i) List.filter_sublist step))

/-- The three-incidence form of the common-order deletion bound. -/
theorem fullBridgeFree_increasing_subsequences (paths : Fin p → List (Fin n))
    (simple : ∀ i, (paths i).Nodup) (free : ∀ d, IsEmpty (Bridge (ListBefore paths) d)) :
    ∃ rank : Fin n ≃ Fin n, ∃ kept : Fin p → List (Fin n),
      (∀ i, (kept i).Sublist (paths i)) ∧ (∀ i, ((kept i).map rank).Pairwise (· < ·)) ∧
      (∀ i (nonempty : paths i ≠ []), (paths i).getLast nonempty ∈ kept i) ∧
      (∀ x, (occurrences (fun i => (paths i).toFinset \ (kept i).toFinset) x).card ≤ 3) ∧
      (∑ i, (paths i).length) ≤ (∑ i, (kept i).length)+3*n := by
  obtain ⟨rank,kept,sub,ordered,last,pointwise,loss⟩ := fullBridgeFree_increasing_subsequences_two paths simple free
  exact ⟨rank,kept,sub,ordered,last,fun x => (pointwise x).trans (by decide),by omega⟩

/-- At the original budgets, one DAG forces a constant fraction of the
maximum incidence mass over all fully bridge-free simple path families. -/
theorem theorem14_offline_extremal_lower (n p : ℕ) (hn : 2 ≤ n) (hp : p ≤ n^2) :
    ∃ (G : Arcs (Fin n)) (D : Finset (Fin n × Fin n)), IsDAG G ∧ D.card = p ∧
      ∀ H ⊆ G, Preserves G H D.toList →
        ∀ paths : Fin p → List (Fin n), (∀ i, (paths i).Nodup) →
          (∀ d, IsEmpty (Bridge (ListBefore paths) d)) → (∑ i, (paths i).length) ≤ 24*H.card := by
  by_cases noDemands : p = 0
  · subst p
    refine ⟨∅,∅,?_,by simp,?_⟩
    · intro u v edge
      simp [Edge] at edge
    · intro H _ _ _ _ _
      simp
  have hp0 : 0 < p := Nat.pos_of_ne_zero noDemands
  obtain ⟨maximizer,simple,nonempty,full,maximal,_⟩ :=
    theorem14_offline_upper_by_bridge_mass.{0} n p (by omega) hp0
  let M := ∑ i, (maximizer i).length
  have upper (paths : Fin p → List (Fin n)) (simple : ∀ i, (paths i).Nodup)
      (free : ∀ d, IsEmpty (Bridge (ListBefore paths) d)) : (∑ i, (paths i).length) ≤ M :=
    maximal paths simple (fun _ _ _ => free _)
  by_cases dense : 6*n ≤ M
  · have free (d : ℕ) : IsEmpty (Bridge (ListBefore maximizer) d) := full (d+2) le_rfl
    obtain ⟨rank,kept,sub,ordered,last,_,loss⟩ := fullBridgeFree_increasing_subsequences maximizer simple free
    have keptNonempty (i : Fin p) : kept i ≠ [] := List.ne_nil_of_mem (last i (nonempty i))
    have retained : M ≤ 2*(∑ i, (kept i).length) := by change M ≤ _ at loss; omega
    obtain ⟨G,D,acyclic,count,forces⟩ := theorem14_lower_of_increasing_subsequences
      hn hp maximizer kept rank simple keptNonempty free sub ordered retained
    exact ⟨G,D,acyclic,count,fun H subset served paths simple free =>
      (upper paths simple free).trans (forces H subset served)⟩
  · obtain ⟨G,D,acyclic,count,forces⟩ := offline_linear_vertex_lower hn hp0 hp
    refine ⟨G,D,acyclic,count,fun H subset served paths simple free => (upper paths simple free).trans ?_⟩
    have lower := forces H subset served
    omega

end OnlineReachabilityPreservers
