import OnlineReachabilityPreservers.CyclicIntersections

/-! Sparse outgoing rows in a fully bridge-free system. -/

namespace OnlineReachabilityPreservers

open Finset

local notation "ListBefore" => SourceAudit.BeforeIn

variable {V I : Type*} [DecidableEq V]

/-- An edge between consecutive vertices of one simple list path. -/
def ConsecutiveListStep (paths : I → List V) (row : I) (u v : V) : Prop :=
  ListBefore paths row u v ∧ (paths row).idxOf u+1 = (paths row).idxOf v

private structure ConsecutiveChain (paths : I → List V) (vertices : Finset V) (k : ℕ) where
  vertex : Fin (k+1) → V
  row : Fin k → I
  distinctVertices : Function.Injective vertex
  distinctRows : Function.Injective row
  inside : ∀ j, vertex j ∈ vertices
  step : ∀ j, ConsecutiveListStep paths (row j) (vertex j.castSucc) (vertex j.succ)

private def ConsecutiveChain.append {paths : I → List V} {S : Finset V} {k : ℕ}
    (c : ConsecutiveChain paths S k) {w : V} {row : I}
    (inside : w ∈ S) (newVertex : w ∉ Set.range c.vertex) (newRow : row ∉ Set.range c.row)
    (step : ConsecutiveListStep paths row (c.vertex (Fin.last k)) w) : ConsecutiveChain paths S (k+1) where
  vertex := Fin.snoc c.vertex w
  row := Fin.snoc c.row row
  distinctVertices := Fin.snoc_injective_of_injective c.distinctVertices newVertex
  distinctRows := Fin.snoc_injective_of_injective c.distinctRows newRow
  inside j := by
    refine Fin.lastCases ?_ (fun i => ?_) j
    · simpa only [Fin.snoc_last] using inside
    · simpa only [Fin.snoc_castSucc] using c.inside i
  step j := by
    refine Fin.lastCases ?_ (fun i => ?_) j
    · simpa only [Fin.snoc_castSucc,Fin.snoc_last,Fin.succ_last] using step
    · have exchange : i.castSucc.succ = i.succ.castSucc := Fin.ext rfl
      simpa only [exchange,Fin.snoc_castSucc] using c.step i

private theorem longestConsecutiveChain [Fintype V] (paths : I → List V) {S : Finset V} (nonempty : S.Nonempty) :
    ∃ k, Nonempty (ConsecutiveChain paths S k) ∧
      ∀ k', Nonempty (ConsecutiveChain paths S k') → k' ≤ k := by
  classical
  let available := (range (Fintype.card V+1)).filter fun k => Nonempty (ConsecutiveChain paths S k)
  obtain ⟨initial,member⟩ := nonempty
  have zero : Nonempty (ConsecutiveChain paths S 0) :=
    ⟨{ vertex := fun _ => initial
       row := Fin.elim0
       distinctVertices := fun i j _ => Fin.ext (by have := i.isLt; have := j.isLt; omega)
       distinctRows := fun {i} => Fin.elim0 i
       inside := fun _ => member
       step := fun i => Fin.elim0 i }⟩
  have someLength : available.Nonempty := ⟨0,mem_filter.mpr ⟨mem_range.mpr (by omega),zero⟩⟩
  obtain ⟨k,found,best⟩ := exists_max_image available id someLength
  refine ⟨k,(mem_filter.mp found).2,fun k' valid => best k' ?_⟩
  obtain ⟨c⟩ := valid
  have cap := Fintype.card_le_of_injective c.vertex c.distinctVertices
  simp only [Fintype.card_fin] at cap
  exact mem_filter.mpr ⟨mem_range.mpr (by omega),⟨c⟩⟩

private theorem consecutiveChain_no_river {paths : I → List V} {S : Finset V} {k : ℕ}
    (free : ∀ d, IsEmpty (Bridge (ListBefore paths) d)) (c : ConsecutiveChain paths S k)
    {start finish : Fin (k+1)} (forward : start < finish) {river : I}
    (riverStep : ListBefore paths river (c.vertex start) (c.vertex finish))
    (apart : ∀ j, start.val ≤ j.val → j.val < finish.val → river ≠ c.row j) : False := by
  let d := finish.val-start.val-1
  have ordered : start.val < finish.val := forward
  have fits := finish.isLt
  have endpoint : start.val+(d+1) = finish.val := by dsimp [d]; omega
  let vertexIndex (j : Fin (d+2)) : Fin (k+1) := ⟨start.val+j.val,by have := j.isLt; omega⟩
  let rowIndex (j : Fin (d+1)) : Fin k := ⟨start.val+j.val,by have := j.isLt; omega⟩
  have indexV : Function.Injective vertexIndex := by
    intro i j same
    apply Fin.ext
    exact Nat.add_left_cancel (congrArg Fin.val same)
  have indexR : Function.Injective rowIndex := by
    intro i j same
    apply Fin.ext
    exact Nat.add_left_cancel (congrArg Fin.val same)
  have first : vertexIndex 0 = start := Fin.ext (Nat.add_zero _)
  have last : vertexIndex (Fin.last (d+1)) = finish := Fin.ext endpoint
  let bridge : Bridge (ListBefore paths) d :=
    { vertex := c.vertex ∘ vertexIndex
      arc := c.row ∘ rowIndex
      river := river
      distinctVertices := c.distinctVertices.comp indexV
      distinctArcs := c.distinctRows.comp indexR
      river_ne_arc := fun j => apart (rowIndex j) (by dsimp [rowIndex]; omega)
        (by have := j.isLt; dsimp [rowIndex]; omega)
      riverStep := by simpa only [Function.comp_apply,first,last] using riverStep
      arcStep := fun j => by
        have atStart : vertexIndex j.castSucc = (rowIndex j).castSucc := Fin.ext rfl
        have atEnd : vertexIndex j.succ = (rowIndex j).succ := Fin.ext (Nat.add_assoc _ _ _).symm
        simpa only [Function.comp_apply,atStart,atEnd] using (c.step (rowIndex j)).1 }
  exact (free d).false bridge

private theorem consecutiveChain_no_river_from_end {paths : I → List V} {S : Finset V} {k : ℕ}
    (free : ∀ d, IsEmpty (Bridge (ListBefore paths) d)) (c : ConsecutiveChain paths S k)
    {start finish : Fin (k+1)} (forward : start ≤ finish) (beforeLast : finish.val < k)
    {firstRow river : I} (different : river ≠ firstRow)
    (firstStep : ListBefore paths firstRow (c.vertex (Fin.last k)) (c.vertex start))
    (riverStep : ListBefore paths river (c.vertex (Fin.last k)) (c.vertex finish))
    (apart : ∀ j, start.val ≤ j.val → j.val < finish.val → firstRow ≠ c.row j ∧ river ≠ c.row j) : False := by
  let d := finish.val-start.val
  have ordered : start.val ≤ finish.val := forward
  have endpoint : start.val+d = finish.val := Nat.add_sub_of_le ordered
  let vertexIndex (j : Fin (d+1)) : Fin (k+1) := ⟨start.val+j.val,by have := j.isLt; omega⟩
  let rowIndex (j : Fin d) : Fin k := ⟨start.val+j.val,by have := j.isLt; omega⟩
  let otherVertices := c.vertex ∘ vertexIndex
  let otherRows := c.row ∘ rowIndex
  have vertexInj : Function.Injective otherVertices := c.distinctVertices.comp (by
    intro i j same
    apply Fin.ext
    exact Nat.add_left_cancel (congrArg Fin.val same))
  have rowInj : Function.Injective otherRows := c.distinctRows.comp (by
    intro i j same
    apply Fin.ext
    exact Nat.add_left_cancel (congrArg Fin.val same))
  have freshVertex : c.vertex (Fin.last k) ∉ Set.range otherVertices := by
    rintro ⟨j,equal⟩
    have index := congrArg Fin.val (c.distinctVertices equal)
    change start.val+j.val = k at index
    have := j.isLt
    omega
  have freshRow : firstRow ∉ Set.range otherRows := by
    rintro ⟨j,equal⟩
    have := j.isLt
    have info := apart (rowIndex j) (by dsimp [rowIndex]; omega) (by dsimp [rowIndex]; omega)
    exact info.1 equal.symm
  have first : vertexIndex 0 = start := Fin.ext (Nat.add_zero _)
  have last : vertexIndex (Fin.last d) = finish := Fin.ext endpoint
  let bridge : Bridge (ListBefore paths) d :=
    { vertex := Fin.cons (c.vertex (Fin.last k)) otherVertices
      arc := Fin.cons firstRow otherRows
      river := river
      distinctVertices := Fin.cons_injective_of_injective freshVertex vertexInj
      distinctArcs := Fin.cons_injective_of_injective freshRow rowInj
      river_ne_arc := fun j => Fin.cases different (fun i => (apart (rowIndex i)
        (by dsimp [rowIndex]; omega) (by have := i.isLt; dsimp [rowIndex]; omega)).2) j
      riverStep := by
        rw [← Fin.succ_last d,Fin.cons_succ,Fin.cons_zero]
        simpa only [otherVertices,Function.comp_apply,last] using riverStep
      arcStep := fun j => by
        refine Fin.cases ?_ (fun i => ?_) j
        · change ListBefore paths firstRow (c.vertex (Fin.last k)) (c.vertex (vertexIndex 0))
          simpa only [first] using firstStep
        · have exchange : i.succ.castSucc = i.castSucc.succ := Fin.ext rfl
          have atStart : vertexIndex i.castSucc = (rowIndex i).castSucc := Fin.ext rfl
          have atEnd : vertexIndex i.succ = (rowIndex i).succ := Fin.ext (Nat.add_assoc _ _ _).symm
          rw [exchange,Fin.cons_succ,Fin.cons_succ,Fin.cons_succ]
          simpa only [otherRows,otherVertices,Function.comp_apply,atStart,atEnd] using (c.step (rowIndex i)).1 }
  exact (free d).false bridge

private theorem ConsecutiveChain.end_before_earlier_row {paths : I → List V} {S : Finset V} {k : ℕ}
    (free : ∀ d, IsEmpty (Bridge (ListBefore paths) d)) (c : ConsecutiveChain paths S k)
    {j : Fin k} (notLast : j.val+1 < k) (onRow : c.vertex (Fin.last k) ∈ paths (c.row j)) :
    ListBefore paths (c.row j) (c.vertex (Fin.last k)) (c.vertex j.castSucc) := by
  have chosen := c.step j
  have apart : c.vertex (Fin.last k) ≠ c.vertex j.castSucc := by
    intro equal
    have index := congrArg Fin.val (c.distinctVertices equal)
    change k = j.val at index
    omega
  rcases listBefore_total onRow chosen.1.1 apart with before | after
  · exact before
  · have later : ListBefore paths (c.row j) (c.vertex j.succ) (c.vertex (Fin.last k)) := by
      refine ⟨chosen.1.2.1,onRow,?_⟩
      have h1 := after.2.2
      have h2 := chosen.2
      have notEqual : (paths (c.row j)).idxOf (c.vertex j.succ) ≠
          (paths (c.row j)).idxOf (c.vertex (Fin.last k)) := by
        intro equal
        have sameVertex := (List.idxOf_inj chosen.1.2.1).mp equal
        have sameIndex := congrArg Fin.val (c.distinctVertices sameVertex)
        change j.val+1 = k at sameIndex
        omega
      omega
    exfalso
    apply consecutiveChain_no_river free c (start := j.succ) (finish := Fin.last k) notLast later
    intro i afterStart _ equal
    have same := congrArg Fin.val (c.distinctRows equal)
    change j.val+1 ≤ i.val at afterStart
    omega

variable [Fintype V] [Fintype I]

/-- Count the rows offering a consecutive step from `t` into the set. -/
noncomputable def consecutiveOutgoingRows (paths : I → List V) (S : Finset V) (t : V) : Finset I := by
  classical
  exact univ.filter fun row => ∃ w ∈ S, ConsecutiveListStep paths row t w

/-- In every nonempty vertex subset there is a vertex with outgoing
consecutive steps on at most three distinct rows. -/
theorem exists_consecutiveOutgoingRows_le_three (paths : I → List V)
    (free : ∀ d, IsEmpty (Bridge (ListBefore paths) d)) {S : Finset V} (nonempty : S.Nonempty) :
    ∃ t ∈ S, (consecutiveOutgoingRows paths S t).card ≤ 3 := by
  classical
  obtain ⟨k,⟨c⟩,longest⟩ := longestConsecutiveChain paths nonempty
  let t := c.vertex (Fin.last k)
  let out := consecutiveOutgoingRows paths S t
  let unused := out.filter fun row => row ∉ Set.range c.row
  let last := out.filter fun row => ∃ i, c.row i = row ∧ i.val+1 = k
  let earlier := out.filter fun row => ∃ i, c.row i = row ∧ i.val+1 < k
  have target {row : I} (outgoing : row ∈ out) : ∃ w ∈ S, ConsecutiveListStep paths row t w :=
    (mem_filter.mp outgoing).2
  have covered : out ⊆ unused ∪ last ∪ earlier := by
    intro row member
    by_cases used : row ∈ Set.range c.row
    · obtain ⟨i,rfl⟩ := used
      by_cases atEnd : i.val+1 = k
      · exact mem_union.mpr (Or.inl (mem_union.mpr (Or.inr (mem_filter.mpr ⟨member,i,rfl,atEnd⟩))))
      · exact mem_union.mpr (Or.inr (mem_filter.mpr ⟨member,i,rfl,by have := i.isLt; omega⟩))
    · exact mem_union.mpr (Or.inl (mem_union.mpr (Or.inl (mem_filter.mpr ⟨member,used⟩))))
  have oldTarget {row : I} {w : V} (freshRow : row ∉ Set.range c.row) (inSet : w ∈ S)
      (step : ConsecutiveListStep paths row t w) : ∃ i, c.vertex i = w ∧ i.val < k := by
    by_cases existing : w ∈ Set.range c.vertex
    · obtain ⟨i,rfl⟩ := existing
      refine ⟨i,rfl,?_⟩
      by_contra! atEnd
      have lastIndex : i = Fin.last k := by
        apply Fin.ext
        change i.val = k
        have := i.isLt
        omega
      exact listBefore_ne step.1 (congrArg c.vertex lastIndex.symm)
    · have impossible := longest (k+1) ⟨c.append inSet existing freshRow step⟩
      omega
  have unusedCount : unused.card ≤ 1 := by
    apply card_le_one_iff.mpr
    intro i j hi hj
    by_contra distinct
    obtain ⟨wi,insideI,stepI⟩ := target (mem_filter.mp hi).1
    obtain ⟨wj,insideJ,stepJ⟩ := target (mem_filter.mp hj).1
    have freshI := (mem_filter.mp hi).2
    have freshJ := (mem_filter.mp hj).2
    obtain ⟨xi,rfl,earlyI⟩ := oldTarget freshI insideI stepI
    obtain ⟨xj,rfl,earlyJ⟩ := oldTarget freshJ insideJ stepJ
    have noBoth {i j : I} {a b : Fin (k+1)} (before : a ≤ b) (early : b.val < k)
        (different : j ≠ i) (unusedI : i ∉ Set.range c.row) (unusedJ : j ∉ Set.range c.row)
        (first : ListBefore paths i t (c.vertex a)) (second : ListBefore paths j t (c.vertex b)) : False :=
      consecutiveChain_no_river_from_end free c before early different first second
        (fun q _ _ => ⟨fun equal => unusedI ⟨q,equal.symm⟩,fun equal => unusedJ ⟨q,equal.symm⟩⟩)
    rcases le_total xi xj with order | order
    · exact noBoth order earlyJ (fun equal => distinct equal.symm) freshI freshJ stepI.1 stepJ.1
    · exact noBoth order earlyI distinct freshJ freshI stepJ.1 stepI.1
  have lastCount : last.card ≤ 1 := by
    apply card_le_one_iff.mpr
    intro i j hi hj
    obtain ⟨a,rfl,atEndA⟩ := (mem_filter.mp hi).2
    obtain ⟨b,rfl,atEndB⟩ := (mem_filter.mp hj).2
    exact congrArg c.row (Fin.ext (by omega))
  have earlyCount : earlier.card ≤ 1 := by
    apply card_le_one_iff.mpr
    intro i j hi hj
    by_contra distinct
    obtain ⟨a,rfl,earlyA⟩ := (mem_filter.mp hi).2
    obtain ⟨b,rfl,earlyB⟩ := (mem_filter.mp hj).2
    obtain ⟨_,_,stepA⟩ := target (mem_filter.mp hi).1
    obtain ⟨_,_,stepB⟩ := target (mem_filter.mp hj).1
    have beforeA := c.end_before_earlier_row free earlyA stepA.1.1
    have beforeB := c.end_before_earlier_row free earlyB stepB.1.1
    have noBoth {a b : Fin k} (order : a < b) (early : b.val+1 < k)
        (left : ListBefore paths (c.row a) t (c.vertex a.castSucc))
        (right : ListBefore paths (c.row b) t (c.vertex b.castSucc)) : False := by
      have first : ListBefore paths (c.row a) t (c.vertex a.succ) :=
        ⟨left.1,(c.step a).1.2.1,left.2.2.trans (c.step a).1.2.2⟩
      have chain : a.succ ≤ b.castSucc := by change a.val+1 ≤ b.val; exact order
      apply consecutiveChain_no_river_from_end free c chain (by exact Nat.lt_of_succ_lt early)
        (fun equal => order.ne (c.distinctRows equal).symm) first right
      intro q afterStart beforeEnd
      change a.val+1 ≤ q.val at afterStart
      change q.val < b.val at beforeEnd
      exact ⟨fun equal => by have := congrArg Fin.val (c.distinctRows equal); omega,
        fun equal => by have := congrArg Fin.val (c.distinctRows equal); omega⟩
    rcases lt_or_gt_of_ne (fun equal => distinct (congrArg c.row equal)) with order | order
    · exact noBoth order earlyB beforeA beforeB
    · exact noBoth order earlyA beforeB beforeA
  refine ⟨t,c.inside _,(card_le_card covered).trans ?_⟩
  have total := card_union_le (unused ∪ last) earlier
  have first := card_union_le unused last
  omega

end OnlineReachabilityPreservers
