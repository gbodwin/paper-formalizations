import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.Finite

/-! Order the components of a graph of maximum degree two for sparse block cuts. -/

namespace OnlineReachabilityPreservers

open Finset SimpleGraph

variable {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]

private theorem degreeTwo_neighbor_eq {v left right x : V} (degree : G.degree v ≤ 2)
    (distinct : left ≠ right) (first : G.Adj v left) (second : G.Adj v right) (other : G.Adj v x) :
    x = left ∨ x = right := by
  classical
  have contains : ({left,right} : Finset V) ⊆ G.neighborFinset v := by
    intro label member
    rw [G.mem_neighborFinset]
    rcases mem_insert.mp member with rfl | last
    · exact first
    · obtain rfl := mem_singleton.mp last
      exact second
  have fitted : (G.neighborFinset v).card ≤ ({left,right} : Finset V).card := by
    rw [card_pair distinct,G.card_neighborFinset_eq_degree]
    exact degree
  have equal := eq_of_subset_of_card_le contains fitted
  have seen : x ∈ G.neighborFinset v := (G.mem_neighborFinset _ _).mpr other
  rw [← equal] at seen
  simpa only [mem_insert,mem_singleton] using seen

private theorem degreeTwo_interior_neighbor (degree : ∀ v, G.degree v ≤ 2)
    {u v : V} (path : G.Walk u v) (simple : path.IsPath) {i : ℕ}
    (positive : 0 < i) (internal : i < path.length) {x : V} (adjacent : G.Adj (path.getVert i) x) :
    x = path.getVert (i-1) ∨ x = path.getVert (i+1) := by
  have predecessor : G.Adj (path.getVert (i-1)) (path.getVert i) := by
    simpa only [show i-1+1 = i by omega] using path.adj_getVert_succ (i := i-1) (by omega)
  have successor := path.adj_getVert_succ internal
  have distinct : path.getVert (i-1) ≠ path.getVert (i+1) := by
    intro same
    have indices := simple.getVert_injOn (show i-1 ≤ path.length by omega)
      (show i+1 ≤ path.length by omega) same
    omega
  exact degreeTwo_neighbor_eq G (degree _) distinct predecessor.symm successor adjacent

omit [DecidableRel G.Adj] in
private theorem longestComponentPath (c : G.ConnectedComponent) :
    ∃ u v, ∃ path : G.Walk u v, u ∈ c.supp ∧ path.IsPath ∧
      ∀ a b (other : G.Walk a b), a ∈ c.supp → other.IsPath → other.length ≤ path.length := by
  classical
  let possible (length : ℕ) := ∃ u v, ∃ path : G.Walk u v,
    u ∈ c.supp ∧ path.IsPath ∧ path.length = length
  let lengths := (range (Fintype.card V)).filter possible
  obtain ⟨anchor,rfl⟩ := c.exists_rep
  have present : anchor ∈ (G.connectedComponentMk anchor).supp := by simp
  have possible0 : possible 0 := ⟨anchor,anchor,.nil,present,SimpleGraph.Walk.IsPath.nil,rfl⟩
  have positive : 0 < Fintype.card V := Fintype.card_pos_iff.mpr ⟨anchor⟩
  have nonempty : lengths.Nonempty := ⟨0,mem_filter.mpr ⟨mem_range.mpr positive,possible0⟩⟩
  obtain ⟨k,member,largest⟩ := exists_max_image lengths id nonempty
  obtain ⟨u,v,path,inside,simple,exactLength⟩ := (mem_filter.mp member).2
  refine ⟨u,v,path,inside,simple,?_⟩
  intro a b other starts isPath
  have offered : other.length ∈ lengths := mem_filter.mpr
    ⟨mem_range.mpr isPath.length_lt,⟨a,b,other,starts,isPath,rfl⟩⟩
  rw [exactLength]
  exact largest _ offered

/-- A finite graph of maximum degree two has a spanning simple path in
each component. Every component edge joins neighboring positions in
that path, or its two endpoints. -/
theorem degreeTwo_component_path (degree : ∀ v, G.degree v ≤ 2) (c : G.ConnectedComponent) :
    ∃ u v, ∃ path : G.Walk u v, path.IsPath ∧
      (∀ x, x ∈ path.support ↔ x ∈ c.supp) ∧
      ∀ i j, i ≤ path.length → j ≤ path.length → G.Adj (path.getVert i) (path.getVert j) →
        i+1 = j ∨ j+1 = i ∨ (i = 0 ∧ j = path.length) ∨ (j = 0 ∧ i = path.length) := by
  obtain ⟨u,v,path,starts,simple,longest⟩ := longestComponentPath G c
  have ends : v ∈ c.supp := by
    rw [SimpleGraph.ConnectedComponent.mem_supp_iff] at starts ⊢
    exact (SimpleGraph.ConnectedComponent.sound path.reachable).symm.trans starts
  have firstClosed {x : V} (adjacent : G.Adj u x) : x ∈ path.support := by
    by_contra outside
    have longer := longest x v (path.cons adjacent.symm) (c.mem_supp_of_adj_mem_supp starts adjacent)
      (simple.cons outside)
    simp only [SimpleGraph.Walk.length_cons] at longer
    omega
  have lastClosed {x : V} (adjacent : G.Adj v x) : x ∈ path.support := by
    by_contra outside
    have reverseOutside : x ∉ path.reverse.support := by
      simpa only [SimpleGraph.Walk.support_reverse,List.mem_reverse] using outside
    have reversed := (path.isPath_reverse_iff).mpr simple
    have longer := longest x u (path.reverse.cons adjacent.symm) (c.mem_supp_of_adj_mem_supp ends adjacent)
      (reversed.cons reverseOutside)
    simp only [SimpleGraph.Walk.length_cons,SimpleGraph.Walk.length_reverse] at longer
    omega
  have closed {y x : V} (visible : y ∈ path.support) (adjacent : G.Adj y x) : x ∈ path.support := by
    obtain ⟨i,rfl,bounded⟩ := SimpleGraph.Walk.mem_support_iff_exists_getVert.mp visible
    by_cases start : i = 0
    · apply firstClosed
      simpa only [start,SimpleGraph.Walk.getVert_zero] using adjacent
    by_cases finish : i = path.length
    · apply lastClosed
      simpa only [finish,SimpleGraph.Walk.getVert_length] using adjacent
    rcases degreeTwo_interior_neighbor G degree path simple (by omega) (by omega) adjacent with rfl | rfl
    · exact path.getVert_mem_support _
    · exact path.getVert_mem_support _
  refine ⟨u,v,path,simple,?_,?_⟩
  · intro x
    constructor
    · intro visible
      obtain ⟨before,_,_⟩ := path.mem_support_iff_exists_append.mp visible
      rw [SimpleGraph.ConnectedComponent.mem_supp_iff] at starts ⊢
      exact (SimpleGraph.ConnectedComponent.sound before.reachable).symm.trans starts
    · intro inside
      have reachable := (G.reachable_iff_reflTransGen u x).mp (c.reachable_of_mem_supp starts inside)
      clear inside
      induction reachable with
      | refl => exact path.start_mem_support
      | tail _ edge ih => exact closed ih edge
  · intro i j hi hj edge
    by_cases first : 0 < i ∧ i < path.length
    · rcases degreeTwo_interior_neighbor G degree path simple first.1 first.2 edge with back | forward
      · have equal := simple.getVert_injOn hj (show i-1 ≤ path.length by omega) back
        omega
      · have equal := simple.getVert_injOn hj (show i+1 ≤ path.length by omega) forward
        omega
    by_cases second : 0 < j ∧ j < path.length
    · rcases degreeTwo_interior_neighbor G degree path simple second.1 second.2 edge.symm with back | forward
      · have equal := simple.getVert_injOn hi (show j-1 ≤ path.length by omega) back
        omega
      · have equal := simple.getVert_injOn hi (show j+1 ≤ path.length by omega) forward
        omega
    have apart : i ≠ j := fun equal => edge.ne (congrArg path.getVert equal)
    omega

omit [Fintype V] in
private theorem order_get_inside [DecidableEq V] {order front middle suffix : List V}
    (layout : order = front++middle++suffix) (simple : order.Nodup) (i : ℕ) (inside : i < middle.length) :
    order.idxOf middle[i] = front.length+i := by
  have fits : front.length+i < order.length := by
    rw [layout]
    simp only [List.length_append]
    omega
  have value : order[front.length+i] = middle[i] := by
    subst order
    rw [List.getElem_append_left (by rw [List.length_append]; omega)]
    rw [List.getElem_append_right (by omega)]
    simp only [Nat.add_sub_cancel_left]
  rw [← value, simple.idxOf_getElem]

private theorem blockBoundary_between {width x y : ℕ} (positive : 0 < width) (different : x/width < y/width) :
    x ≤ (x/width+1)*width-1 ∧ (x/width+1)*width ≤ y := by
  have before := (Nat.div_lt_iff_lt_mul positive).mp (Nat.lt_succ_self (x/width))
  change x < (x/width+1)*width at before
  have after := (Nat.le_div_iff_mul_le positive).mp (show x/width+1 ≤ y/width by omega)
  omega

/-- Order every vertex into consecutive blocks of the prescribed width.
At most two discarded vertices per block boundary eliminate all edges
between different blocks of a graph of maximum degree two. -/
theorem degreeTwo_block_order [DecidableEq V] (degree : ∀ v, G.degree v ≤ 2)
    (width : ℕ) (positive : 0 < width) :
    ∃ order : List V, order.Nodup ∧ (∀ x, x ∈ order) ∧
      ∃ removed : Finset V, removed.card ≤ 2*((Fintype.card V-1)/width) ∧
        ∀ ⦃x y⦄, G.Adj x y → x ∉ removed → y ∉ removed → order.idxOf x/width = order.idxOf y/width := by
  classical
  let C := G.ConnectedComponent
  let : Fintype C := Fintype.ofFinite _
  choose start stop path simple memPath steps using degreeTwo_component_path G degree
  let components := (univ : Finset C).toList
  let block (c : C) := (path c).support
  let order := components.flatMap block
  have allComponents (c : C) : c ∈ components := by simp [components]
  have disjointBlocks : components.Pairwise (fun a b => List.Disjoint (block a) (block b)) := by
    apply (Finset.nodup_toList univ).imp
    intro a b apart x inA inB
    have aComponent := (a.mem_supp_iff x).mp ((memPath a x).mp inA)
    have bComponent := (b.mem_supp_iff x).mp ((memPath b x).mp inB)
    exact apart (aComponent.symm.trans bComponent)
  have orderSimple : order.Nodup := List.nodup_flatMap.mpr
    ⟨fun c _ => (simple c).support_nodup,disjointBlocks⟩
  have all (x : V) : x ∈ order := by
    refine List.mem_flatMap.mpr ⟨G.connectedComponentMk x,allComponents _,?_⟩
    exact (memPath _ x).mpr (by simp)
  have count : order.length = Fintype.card V := by
    have every : order.toFinset = univ := eq_univ_of_forall fun x => List.mem_toFinset.mpr (all x)
    rw [← List.toFinset_card_of_nodup orderSimple,every,card_univ]
  let cuts := (order.length-1)/width
  let boundary (j : Fin cuts) := (j.val+1)*width-1
  have cutFits (j : Fin cuts) : boundary j < order.length := by
    have within := (Nat.le_div_iff_mul_le positive).mp (show j.val+1 ≤ (order.length-1)/width from j.isLt)
    have nonzero : 0 < (j.val+1)*width := Nat.mul_pos (Nat.succ_pos _) positive
    dsimp only [boundary]
    omega
  let atCut (j : Fin cuts) := order[boundary j]'(cutFits j)
  let startOfCut (j : Fin cuts) := start (G.connectedComponentMk (atCut j))
  let removed := (univ : Finset (Fin cuts)).image atCut ∪ (univ : Finset (Fin cuts)).image startOfCut
  have removedSize : removed.card ≤ 2*((Fintype.card V-1)/width) := by
    have total := card_union_le ((univ : Finset (Fin cuts)).image atCut) ((univ : Finset (Fin cuts)).image startOfCut)
    have first : ((univ : Finset (Fin cuts)).image atCut).card ≤ cuts := card_image_le.trans (by simp)
    have last : ((univ : Finset (Fin cuts)).image startOfCut).card ≤ cuts := card_image_le.trans (by simp)
    have expression : cuts = (Fintype.card V-1)/width := by rw [← count]
    change removed.card ≤ _ at total
    omega
  have betweenCut {x y : V} (edge : G.Adj x y) (before : order.idxOf x/width < order.idxOf y/width) : x ∈ removed := by
    let c := G.connectedComponentMk x
    have atX : x ∈ c.supp := by simp [c]
    have atY : y ∈ c.supp := c.mem_supp_of_adj_mem_supp atX edge
    obtain ⟨i,xi,hi⟩ := SimpleGraph.Walk.mem_support_iff_exists_getVert.mp ((memPath c x).mpr atX)
    obtain ⟨j,yj,hj⟩ := SimpleGraph.Walk.mem_support_iff_exists_getVert.mp ((memPath c y).mpr atY)
    obtain ⟨earlier,later,compsLayout⟩ := List.mem_iff_append.mp (allComponents c)
    let front := earlier.flatMap block
    have layout : order = front++block c++later.flatMap block := by
      dsimp only [order,front]
      rw [compsLayout,List.flatMap_append,List.flatMap_cons,List.append_assoc]
    have positions (k : ℕ) (valid : k ≤ (path c).length) :
        order.idxOf ((path c).getVert k) = front.length+k := by
      rw [(path c).getVert_eq_support_getElem valid]
      exact order_get_inside layout orderSimple k (by rw [(path c).length_support]; omega)
    have posX : order.idxOf x = front.length+i := xi ▸ positions i hi
    have posY : order.idxOf y = front.length+j := yj ▸ positions j hj
    have sorted : i < j := by
      by_contra h
      have ranked : order.idxOf y ≤ order.idxOf x := by omega
      exact (not_le_of_gt before) (Nat.div_le_div_right ranked)
    let q := order.idxOf x/width
    obtain ⟨low,high⟩ := blockBoundary_between positive before
    have insideY : order.idxOf y < order.length := List.idxOf_lt_length_of_mem (all y)
    have qFits : q < cuts := by
      apply Nat.lt_of_succ_le
      exact (Nat.le_div_iff_mul_le positive).mpr (high.trans (by omega))
    let cut : Fin cuts := ⟨q,qFits⟩
    have atLeast : order.idxOf x ≤ boundary cut := low
    have beforeY : boundary cut < order.idxOf y := by
      have positiveProduct : 0 < (q+1)*width := Nat.mul_pos (Nat.succ_pos _) positive
      change (q+1)*width-1 < order.idxOf y
      change (q+1)*width ≤ order.idxOf y at high
      omega
    have cutRank : order.idxOf (atCut cut) = boundary cut := orderSimple.idxOf_getElem (boundary cut) (cutFits cut)
    have alternatives := steps c i j hi hj (xi.symm ▸ yj.symm ▸ edge)
    rcases alternatives with step | back | endpoints | flipped
    · have equalRank : order.idxOf x = order.idxOf (atCut cut) := by omega
      have equal : x = atCut cut := (List.idxOf_inj (all x)).mp equalRank
      exact mem_union_left _ (mem_image.mpr ⟨cut,mem_univ _,equal.symm⟩)
    · omega
    · let offset := boundary cut-front.length
      have bounded : offset ≤ (path c).length := by
        dsimp only [offset]
        omega
      have atOffset := positions offset bounded
      have eqRank : order.idxOf (atCut cut) = order.idxOf ((path c).getVert offset) := by
        rw [cutRank,atOffset]
        dsimp only [offset]
        omega
      have eqVert : atCut cut = (path c).getVert offset := (List.idxOf_inj (all (atCut cut))).mp eqRank
      have cutComponent : G.connectedComponentMk (atCut cut) = c :=
        (c.mem_supp_iff _).mp ((memPath c _).mp
          (eqVert ▸ (path c).getVert_mem_support offset))
      have xStarts : x = start c := by rw [← xi,endpoints.1,(path c).getVert_zero]
      have sameStart : startOfCut cut = x := by
        dsimp only [startOfCut]
        rw [cutComponent]
        exact xStarts.symm
      exact mem_union_right _ (mem_image.mpr ⟨cut,mem_univ _,sameStart⟩)
    · omega
  refine ⟨order,orderSimple,all,removed,removedSize,?_⟩
  intro x y edge xSafe ySafe
  by_contra different
  rcases lt_or_gt_of_ne different with first | last
  · exact xSafe (betweenCut edge first)
  · exact ySafe (betweenCut edge.symm last)

end OnlineReachabilityPreservers
