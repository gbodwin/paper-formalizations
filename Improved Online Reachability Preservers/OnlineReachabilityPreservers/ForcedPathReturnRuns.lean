import OnlineReachabilityPreservers.LocalFrozenLowMass
import OnlineReachabilityPreservers.PackedDegreeGaps

/-! Long runs of unsafe cuts in cyclic fully bridge-free systems. -/

namespace OnlineReachabilityPreservers

open Finset
local notation "Before" => SourceAudit.BeforeIn

private def evenVertex {m : ℕ} (i : Fin m) : Fin (2*m-1) := ⟨2*i.val,by omega⟩

private theorem evenVertex_injective {m : ℕ} : Function.Injective (@evenVertex m) := by
  intro a b eq
  have same := congrArg Fin.val eq
  change 2*a.val = 2*b.val at same
  exact Fin.ext (by omega)

private def previousVertex {m : ℕ} (i : Fin (2*m-1)) : Fin (2*m-1) := ⟨i.val-1,by omega⟩

/-- One increasing row on the even vertices and a separate descending
row between each pair of consecutive vertices. -/
def forcedReturnRows {m : ℕ} (i : Fin (2*m-1)) : List (Fin (2*m-1)) :=
  if i.val = 0 then List.ofFn (@evenVertex m) else [i,previousVertex i]

private theorem central_index {m : ℕ} (i : Fin m) :
    (List.ofFn (@evenVertex m)).idxOf (evenVertex i) = i.val := by
  have valid : i.val < (List.ofFn (@evenVertex m)).length := by simp
  have atIndex : (List.ofFn (@evenVertex m))[i.val]'valid = evenVertex i := List.getElem_ofFn valid
  rw [← atIndex,(List.nodup_ofFn.mpr evenVertex_injective).idxOf_getElem]

private theorem forcedReturnRows_nonzero_previous {m : ℕ} {i : Fin (2*m-1)} (nonzero : i.val ≠ 0) :
    i ≠ previousVertex i := by
  intro eq
  have same := congrArg Fin.val eq
  change i.val = i.val-1 at same
  omega

theorem forcedReturnRows_simple {m : ℕ} (i : Fin (2*m-1)) : (forcedReturnRows i).Nodup := by
  unfold forcedReturnRows
  split
  · exact List.nodup_ofFn.mpr evenVertex_injective
  · rename_i nonzero
    simp [forcedReturnRows_nonzero_previous nonzero]

private theorem central_step {m : ℕ} {i x y : Fin (2*m-1)} (zero : i.val = 0)
    (step : Before (@forcedReturnRows m) i x y) : x.val % 2 = 0 ∧ y.val % 2 = 0 ∧ x < y := by
  unfold SourceAudit.BeforeIn at step
  simp only [forcedReturnRows,zero,ite_true] at step
  obtain ⟨a,rfl⟩ := List.mem_ofFn.mp step.1
  obtain ⟨b,rfl⟩ := List.mem_ofFn.mp step.2.1
  rw [central_index,central_index] at step
  change (2*a.val)%2 = 0 ∧ (2*b.val)%2 = 0 ∧ 2*a.val < 2*b.val
  have order := step.2.2
  omega

private theorem descending_step {m : ℕ} {i x y : Fin (2*m-1)} (nonzero : i.val ≠ 0)
    (step : Before (@forcedReturnRows m) i x y) : i = x ∧ y.val+1 = x.val := by
  unfold SourceAudit.BeforeIn at step
  simp only [forcedReturnRows,nonzero,ite_false] at step
  have different := forcedReturnRows_nonzero_previous nonzero
  simp only [List.mem_cons,List.not_mem_nil,or_false] at step
  obtain ⟨xOn,yOn,ordered⟩ := step
  rcases xOn with hx | hx <;> rcases yOn with hy | hy
  · rw [hx,hy] at ordered
    exact (Nat.lt_irrefl _ ordered).elim
  · refine ⟨hx.symm,?_⟩
    rw [hx,hy]
    change i.val-1+1 = i.val
    omega
  · rw [hx,hy] at ordered
    simp [different] at ordered
  · rw [hx,hy] at ordered
    exact (Nat.lt_irrefl _ ordered).elim

private theorem descending_before {m : ℕ} (i : Fin (2*m-1)) (nonzero : i.val ≠ 0) :
    Before (@forcedReturnRows m) i i (previousVertex i) := by
  have different := forcedReturnRows_nonzero_previous nonzero
  simp [SourceAudit.BeforeIn,forcedReturnRows,nonzero,different,different.symm]

/-- Two different rows share at most one vertex. -/
theorem forcedReturnRows_unique_intersections {m : ℕ} {i j x y : Fin (2*m-1)} (distinct : i ≠ j)
    (xi : x ∈ forcedReturnRows i) (yi : y ∈ forcedReturnRows i)
    (xj : x ∈ forcedReturnRows j) (yj : y ∈ forcedReturnRows j) : x = y := by
  by_contra different
  have pair {a : Fin (2*m-1)} (nonzero : a.val ≠ 0) (u : x ∈ forcedReturnRows a) (v : y ∈ forcedReturnRows a) :
      a.val = max x.val y.val ∧ (x.val+1 = y.val ∨ y.val+1 = x.val) := by
    rcases listBefore_total u v different with before | after
    · obtain ⟨rfl,adjacent⟩ := descending_step nonzero before
      exact ⟨(max_eq_left (by omega)).symm,Or.inr adjacent⟩
    · obtain ⟨rfl,adjacent⟩ := descending_step nonzero after
      exact ⟨(max_eq_right (by omega)).symm,Or.inl adjacent⟩
  have even {a v : Fin (2*m-1)} (zero : a.val = 0) (on : v ∈ forcedReturnRows a) : v.val%2 = 0 := by
    simp only [forcedReturnRows,zero,ite_true] at on
    obtain ⟨t,rfl⟩ := List.mem_ofFn.mp on
    change (2*t.val)%2 = 0
    omega
  by_cases ai : i.val = 0
  · have aj : j.val ≠ 0 := fun equal => distinct (Fin.ext (ai.trans equal.symm))
    have ex := even ai xi
    have ey := even ai yi
    rcases (pair aj xj yj).2 with ab | ba <;> omega
  · by_cases aj : j.val = 0
    · have ex := even aj xj
      have ey := even aj yj
      rcases (pair ai xi yi).2 with ab | ba <;> omega
    · exact distinct (Fin.ext ((pair ai xi yi).1.trans (pair aj xj yj).1.symm))

/-- Only the central row and the two neighboring descending rows can
contain a vertex. -/
theorem forcedReturnRows_max_degree {m : ℕ} (x : Fin (2*m-1)) :
    (occurrences (fun i => (forcedReturnRows i).toFinset) x).card ≤ 3 := by
  let candidates : Finset ℕ := {0,x.val,x.val+1}
  have fits (i : Fin (2*m-1)) (on : i ∈ occurrences (fun j => (forcedReturnRows j).toFinset) x) :
      i.val ∈ candidates := by
    have xOn := List.mem_toFinset.mp
      ((mem_occurrences (marks := fun j => (forcedReturnRows j).toFinset)).mp on)
    by_cases zero : i.val = 0
    · simp [candidates,zero]
    · simp only [forcedReturnRows,zero,ite_false,List.mem_cons,List.not_mem_nil,or_false] at xOn
      rcases xOn with same | previous
      · simp [candidates,same]
      · have values := congrArg Fin.val previous
        change x.val = i.val-1 at values
        have next : i.val = x.val+1 := by omega
        simp [candidates,next]
  have count := card_le_card_of_injOn (fun i : Fin (2*m-1) => i.val) fits
    (fun _ _ _ _ same => Fin.ext same)
  refine count.trans ?_
  change ({0,x.val,x.val+1} : Finset ℕ).card ≤ 3
  calc
    _ ≤ ({x.val,x.val+1} : Finset ℕ).card+1 := card_insert_le _ _
    _ ≤ 3 := by
      have pair := card_insert_le x.val ({x.val+1} : Finset ℕ)
      simpa only [card_singleton,Nat.reduceAdd] using Nat.add_le_add_right pair 1

/-- The adjacent descending rows create cycles and full exclusion still
holds at every bridge size. -/
theorem forcedReturnRows_full_free (m k : ℕ) : BridgeFree (Before (@forcedReturnRows m)) k := by
  intro d _
  constructor
  intro b
  by_cases central : b.river.val = 0
  · have upwards := (central_step central b.riverStep).2.2
    have downwards : Antitone b.vertex := Fin.antitone_iff_succ_le.mpr fun i => by
      have nonzero : (b.arc i).val ≠ 0 := fun h => b.river_ne_arc i (Fin.ext (central.trans h.symm))
      have edge := (descending_step nonzero (b.arcStep i)).2
      exact Nat.le_of_lt (by omega)
    exact upwards.not_ge (downwards (Fin.zero_le _))
  · obtain ⟨riverStart,neighbor⟩ := descending_step central b.riverStep
    by_cases even : (b.vertex 0).val % 2 = 0
    · let j := Fin.last d
      have odd : (b.vertex (Fin.last (d+1))).val % 2 ≠ 0 := by omega
      have lastStep : Before (@forcedReturnRows m) (b.arc j)
          (b.vertex j.castSucc) (b.vertex (Fin.last (d+1))) := by
        simpa only [j,Fin.succ_last] using b.arcStep j
      have nonzero : (b.arc j).val ≠ 0 := fun zero => odd (central_step zero lastStep).2.1
      obtain ⟨lastStart,lastNeighbor⟩ := descending_step nonzero lastStep
      apply b.river_ne_arc j
      apply Fin.ext
      rw [riverStart,lastStart]
      omega
    · have firstStep : Before (@forcedReturnRows m) (b.arc 0) (b.vertex 0) (b.vertex (0 : Fin (d+1)).succ) :=
        b.arcStep 0
      have nonzero : (b.arc 0).val ≠ 0 := fun zero => even (central_step zero firstStep).1
      exact b.river_ne_arc 0 (riverStart.trans (descending_step nonzero firstStep).1.symm)

private def centralRow (m : ℕ) (positive : 0 < m) : Fin (2*m-1) := ⟨0,by omega⟩

/-- Every interior cut of the even row has a two-edge return through
its intermediate odd vertex. -/
theorem forcedReturnRows_interior_gap_unsafe {m gap radius : ℕ} (first : 0 < gap) (inside : gap < m)
    (short : 2 ≤ radius) :
    ¬ IsSafePathReturnGap (@forcedReturnRows m) (centralRow m (first.trans inside)) gap radius := by
  let a : Fin m := ⟨gap-1,by omega⟩
  let b : Fin m := ⟨gap,inside⟩
  let x := evenVertex a
  let y := evenVertex b
  let z := previousVertex y
  let root := centralRow m (first.trans inside)
  have ix : (forcedReturnRows root).idxOf x = gap-1 := by simpa [forcedReturnRows,root,centralRow,x,a] using central_index a
  have iy : (forcedReturnRows root).idxOf y = gap := by simpa [forcedReturnRows,root,centralRow,y,b] using central_index b
  have comparison : Before (@forcedReturnRows m) root x y := by
    refine ⟨?_,?_,by rw [ix,iy]; omega⟩
    · simpa [forcedReturnRows,root,centralRow] using (List.mem_ofFn.mpr ⟨a,rfl⟩ : x ∈ List.ofFn (@evenVertex m))
    · simpa [forcedReturnRows,root,centralRow] using (List.mem_ofFn.mpr ⟨b,rfl⟩ : y ∈ List.ofFn (@evenVertex m))
  have yPos : y.val ≠ 0 := by change 2*gap ≠ 0; omega
  have zPos : z.val ≠ 0 := by change 2*gap-1 ≠ 0; omega
  have downTwo : previousVertex z = x := by
    apply Fin.ext
    change 2*gap-1-1 = 2*(gap-1)
    omega
  let G := listPiecePrecedenceGraph (@forcedReturnRows m)
  have firstEdge : Edge G y z := listPiecePrecedenceGraph_edge.mpr ⟨y,descending_before y yPos⟩
  have secondEdge : Edge G z x := by
    rw [← downTwo]
    exact listPiecePrecedenceGraph_edge.mpr ⟨z,descending_before z zPos⟩
  have reaches : y ∈ reachIn G x 2 :=
    reachIn_succ.mpr (Or.inr ⟨z,firstEdge,reachIn_succ.mpr (Or.inr ⟨x,secondEdge,target_mem_reachIn G x 0⟩)⟩)
  intro safe
  apply safe comparison (by rw [ix]; omega) iy.ge
  exact monotone_nat_of_le_succ (reachIn_subset_succ G x) short reaches

private theorem forcedReturnRows_central_length {m : ℕ} (positive : 0 < m) :
    (forcedReturnRows (centralRow m positive)).length = m := by
  simp [forcedReturnRows,centralRow]

/-- The original vertex and row counts are both `2*m-1` and the
incidence mass is `5*m-4`. -/
theorem forcedReturnRows_mass {m : ℕ} (positive : 0 < m) :
    (∑ i : Fin (2*m-1), (forcedReturnRows i).length) = 5*m-4 := by
  let root := centralRow m positive
  let other := (univ : Finset (Fin (2*m-1))).erase root
  have length (i : Fin (2*m-1)) (member : i ∈ other) : (forcedReturnRows i).length = 2 := by
    have nonzero : i.val ≠ 0 := fun eq => (mem_erase.mp member).1 (Fin.ext eq)
    simp [forcedReturnRows,nonzero]
  have count : other.card = (2*m-1)-1 := by simp [other]
  calc
    _ = (∑ i ∈ other, (forcedReturnRows i).length) + (forcedReturnRows root).length :=
      (sum_erase_add _ _ (mem_univ root)).symm
    _ = ((2*m-1)-1)*2+m := by
      rw [sum_congr rfl length, sum_const,smul_eq_mul,count,forcedReturnRows_central_length]
    _ = _ := by omega

/-- Choosing safe gaps leaves the entire even row in one run. -/
theorem forcedReturnRows_safe_run_length {m radius : ℕ} (positive : 0 < m) (short : 2 ≤ radius)
    (cuts : Fin (2*m-1) → Finset ℕ)
    (safe : ∀ i gap, gap ∈ cuts i → IsSafePathReturnGap (@forcedReturnRows m) i gap radius) :
    let root := centralRow m positive
    ((forcedReturnRows root).filter fun x => decide (pathReturnGapRank forcedReturnRows cuts root x = 0)).length = m := by
  let root := centralRow m positive
  have rankZero (x) (on : x ∈ forcedReturnRows root) : pathReturnGapRank forcedReturnRows cuts root x = 0 := by
    unfold pathReturnGapRank degreeReturnGapRank
    refine le_antisymm (Finset.sup_le ?_) (Nat.zero_le _)
    intro gap member
    obtain ⟨chosen,before⟩ := Finset.mem_filter.mp member
    by_contra! gapPos
    change gap ≤ (forcedReturnRows root).idxOf x at before
    have index := List.idxOf_lt_length_of_mem on
    rw [forcedReturnRows_central_length] at index
    exact forcedReturnRows_interior_gap_unsafe gapPos (before.trans_lt index) short
      (safe root gap chosen)
  change ((forcedReturnRows root).filter (fun x => decide (pathReturnGapRank forcedReturnRows cuts root x = 0))).length = m
  rw [List.filter_eq_self.mpr (fun x hx => decide_eq_true (rankZero x hx)),forcedReturnRows_central_length]

/-- The forced run exceeds even the factor-four frozen length cap for
`m ≥ 10`. Both budgets remain positive and at most the mass. -/
theorem forcedReturnRows_above_width {m radius : ℕ} (large : 10 ≤ m) (short : 2 ≤ radius)
    (cuts : Fin (2*m-1) → Finset ℕ)
    (safe : ∀ i gap, gap ∈ cuts i → IsSafePathReturnGap (@forcedReturnRows m) i gap radius) :
    let M := ∑ i : Fin (2*m-1), (forcedReturnRows i).length
    ∃ i r, 4*M/(2*m-1) <
      ((forcedReturnRows i).filter fun x => decide (pathReturnGapRank forcedReturnRows cuts i x = r)).length := by
  have positive : 0 < m := by omega
  refine ⟨centralRow m positive,0,?_⟩
  rw [forcedReturnRows_safe_run_length positive short cuts safe, forcedReturnRows_mass positive]
  apply lt_of_lt_of_le _ large
  apply (Nat.div_lt_iff_lt_mul (by omega)).mpr
  omega

private theorem mapped_path_positions {V W I : Type*} [DecidableEq V] [DecidableEq W]
    (rows : I → List V) (f : V → W) (simple : ∀ i, ((rows i).map f).Nodup)
    {i : I} {v : V} (on : v ∈ rows i) :
    ((rows i).map f).idxOf (f v) = (rows i).idxOf v := by
  have index := List.idxOf_lt_length_of_mem on
  have mapped : (rows i).idxOf v < ((rows i).map f).length := by simpa only [List.length_map]
  have pos := (simple i).idxOf_getElem (i := (rows i).idxOf v) mapped
  rwa [List.getElem_map,List.getElem_idxOf index] at pos

private theorem reachable_on_relabelled_rows {V W : Type*} [LinearOrder V] [LinearOrder W]
    [Fintype V] [Fintype W] {p : ℕ} (rows : Fin p → List V) (f : V → W)
    (simple : ∀ i, ((rows i).map f).Nodup) {x y : V} {radius : ℕ}
    (back : y ∈ reachIn (listPiecePrecedenceGraph rows) x radius) :
      f y ∈ reachIn (listPiecePrecedenceGraph fun i => (rows i).map f) (f x) radius := by
  induction radius generalizing y with
  | zero =>
    simp only [reachIn,mem_singleton] at back ⊢
    exact congrArg f back
  | succ r ih =>
    rcases reachIn_succ.mp back with earlier | ⟨z,edge,rest⟩
    · exact reachIn_succ.mpr (Or.inl (ih earlier))
    · obtain ⟨i,step⟩ := listPiecePrecedenceGraph_edge.mp edge
      exact reachIn_succ.mpr (Or.inr ⟨f z,
        listPiecePrecedenceGraph_edge.mpr ⟨i,listBefore_map f (simple i) step⟩,ih rest⟩)

private theorem pathGapSafe_of_relabelled_rows {V W : Type*} [LinearOrder V] [LinearOrder W]
    [Fintype V] [Fintype W] {p : ℕ} (rows : Fin p → List V) (f : V → W)
    (simple : ∀ i, ((rows i).map f).Nodup) {i : Fin p} {gap radius : ℕ}
    (safe : IsSafePathReturnGap (fun j => (rows j).map f) i gap radius) :
    IsSafePathReturnGap rows i gap radius := by
  intro x y step before after back
  have comparison := listBefore_map f (simple i) step
  have beforeRank := mapped_path_positions rows f simple step.1
  have afterRank := mapped_path_positions rows f simple step.2.1
  exact safe comparison (by rwa [beforeRank]) (by rwa [afterRank])
    (reachable_on_relabelled_rows rows f simple back)

/-- At the prescribed degree stride every vertex of this family keeps
its zero copied label, for every choice of degree gaps. Hence no choice
of safe path gaps brings all runs within the original width. -/
theorem forcedReturnRows_packed_above_width {m radius : ℕ} (large : 10 ≤ m) (short : 2 ≤ radius)
    (degreeCuts pathCuts : Fin (2*m-1) → Finset ℕ) :
    let M := ∑ i : Fin (2*m-1), (forcedReturnRows i).length
    let rows := packListVerticesAtDegreeGaps (@forcedReturnRows m) degreeCuts (3*M/(2*m-1)+1)
    (∀ i gap, gap ∈ pathCuts i → IsSafePathReturnGap rows i gap radius) →
      ∃ i r, 4*M/(2*m-1) <
        ((rows i).filter fun x => decide (pathReturnGapRank rows pathCuts i x = r)).length := by
  let M := ∑ i : Fin (2*m-1), (forcedReturnRows i).length
  let stride := 3*M/(2*m-1)+1
  let rows := packListVerticesAtDegreeGaps (@forcedReturnRows m) degreeCuts stride
  let embed (v : Fin (2*m-1)) : ListVertexBlockIndex (@forcedReturnRows m) stride :=
    ⟨v,⟨0,Nat.succ_pos _⟩⟩
  have injective : Function.Injective embed := fun _ _ eq => congrArg Sigma.fst eq
  have positive : 0 < m := by omega
  have width : 3 < stride := by
    have divisor : 0 < 2*m-1 := by omega
    have le : 3 ≤ 3*M/(2*m-1) := (Nat.le_div_iff_mul_le divisor).mpr (by
      dsimp only [M]
      rw [forcedReturnRows_mass positive]
      omega)
    exact Nat.lt_succ_of_le le
  have originals (i) : rows i = (forcedReturnRows i).map embed :=
    packListVerticesAtDegreeGaps_eq_zero_block _ _ (fun v => (forcedReturnRows_max_degree v).trans_lt width) i
  have simple (i) : ((forcedReturnRows i).map embed).Nodup :=
    (forcedReturnRows_simple i).map injective
  change (∀ i gap, gap ∈ pathCuts i → IsSafePathReturnGap rows i gap radius) → _
  intro safe
  have oldSafe : ∀ i gap, gap ∈ pathCuts i → IsSafePathReturnGap (@forcedReturnRows m) i gap radius :=
    fun i gap chosen => pathGapSafe_of_relabelled_rows (@forcedReturnRows m) embed simple
      (show IsSafePathReturnGap (fun j => (forcedReturnRows j).map embed) i gap radius from
        funext originals ▸ safe i gap chosen)
  obtain ⟨i,r,tooLong⟩ := forcedReturnRows_above_width large short pathCuts oldSafe
  refine ⟨i,r,tooLong.trans_le ?_⟩
  have ranks (v) (member : v ∈ forcedReturnRows i) :
      pathReturnGapRank rows pathCuts i (embed v) = pathReturnGapRank forcedReturnRows pathCuts i v := by
    unfold pathReturnGapRank degreeReturnGapRank
    have pos := mapped_path_positions (@forcedReturnRows m) embed simple member
    rw [← originals i] at pos
    exact congrArg (fun n => ((pathCuts i).filter fun j => j ≤ n).sup id) pos
  have filters : (forcedReturnRows i).filter (fun v => decide (pathReturnGapRank forcedReturnRows pathCuts i v = r)) =
      (forcedReturnRows i).filter (fun v => decide (pathReturnGapRank rows pathCuts i (embed v) = r)) :=
    List.filter_congr (fun v member => by rw [ranks v member])
  change ((forcedReturnRows i).filter (fun v => decide (pathReturnGapRank forcedReturnRows pathCuts i v = r))).length ≤
    ((rows i).filter (fun x => decide (pathReturnGapRank rows pathCuts i x = r))).length
  conv_rhs => rw [originals i,List.filter_map,List.length_map]
  rw [filters]
  exact le_rfl

/-- This family admits a separate frozen witness by the low-mass
construction, with at least an eighth of its original mass. -/
theorem forcedReturnRows_frozen_witness {m k : ℕ} (positive : 0 < m) (cutoff : 2 ≤ k) :
    let M := ∑ i : Fin (2*m-1), (forcedReturnRows i).length
    ∃ n' ≤ 2*m-1, ∃ p' ≤ 2*m-1, ∃ clean : Fin p' → List (Fin n'),
      (∀ i, (clean i).Nodup) ∧ BridgeFree (Before clean) k ∧
      M ≤ 8*(∑ i, (clean i).length) ∧ (∑ i, (clean i).length) ≤ M ∧
      frozenListCaps (2*m-1) (2*m-1) M clean := by
  have nonempty : 0 < 2*m-1 := by omega
  have dense : 2*m-1 ≤ ∑ i : Fin (2*m-1), (forcedReturnRows i).length := by
    rw [forcedReturnRows_mass positive]
    omega
  have half : HalfBridgeFree (Before (@forcedReturnRows m)) k := by
    intro d small b _
    exact (forcedReturnRows_full_free m k small).false b
  refine regularization_list_frozen_low_mass (@forcedReturnRows m) forcedReturnRows_simple half
    cutoff nonempty nonempty dense dense ?_
  rw [forcedReturnRows_mass positive,max_self]
  omega

end OnlineReachabilityPreservers
