import OnlineReachabilityPreservers.BackwardCopyReturns

/-! Combine neighboring safe degree runs while keeping the original caps. -/

namespace OnlineReachabilityPreservers

open Finset
open scoped Sigma.Lex

local notation "Before" => SourceAudit.BeforeIn

private abbrev degreeGapArrivals {n p : ℕ} (paths : Fin p → List (Fin n)) (v : Fin n) :=
  occurrences (fun i => (paths i).toFinset) v

private def degreeGapPrefix {p : ℕ} (arrivals : Finset (Fin p)) (cut : ℕ) : Finset (Fin p) :=
  arrivals.filter fun i => i.val < cut

private theorem degreeGapPrefix_mono {p : ℕ} (arrivals : Finset (Fin p)) :
    Monotone (degreeGapPrefix arrivals) := by
  intro a b order i on
  obtain ⟨arrived,earlier⟩ := mem_filter.mp on
  exact mem_filter.mpr ⟨arrived,earlier.trans_le order⟩

private theorem degreeReturnGapRank_le_arrival {n p : ℕ} (cuts : Fin n → Finset ℕ)
    (v : Fin n) (i : Fin p) : degreeReturnGapRank cuts v i ≤ i.val :=
  Finset.sup_le (fun _ on => (mem_filter.mp on).2)

private theorem degreeReturnGapRank_mono_arrival {n p : ℕ} (cuts : Fin n → Finset ℕ) (v : Fin n) :
    Monotone (degreeReturnGapRank cuts v : Fin p → ℕ) := by
  intro a b arrives
  by_contra! backwards
  obtain ⟨_,_,after,before⟩ := degreeReturnGapRank_lt_iff.mp backwards
  exact after.not_ge (before.trans arrives)

private theorem degreeReturnGapRank_eq_between {n p : ℕ} (cuts : Fin n → Finset ℕ)
    (v : Fin n) {i j : Fin p} (arrives : j ≤ i) (after : degreeReturnGapRank cuts v i ≤ j.val) :
    degreeReturnGapRank cuts v j = degreeReturnGapRank cuts v i := by
  apply le_antisymm (degreeReturnGapRank_mono_arrival cuts v arrives)
  by_contra! strict
  obtain ⟨gap,chosen,early,late⟩ := degreeReturnGapRank_lt_iff.mp strict
  have within : gap ≤ degreeReturnGapRank cuts v i :=
    Finset.le_sup (f := id) (mem_filter.mpr ⟨chosen,late⟩)
  exact early.not_ge (within.trans after)

private noncomputable def packedDegreeReturnCopy {n p : ℕ} (paths : Fin p → List (Fin n))
    (cuts : Fin n → Finset ℕ) (stride : ℕ) (i : Fin p) (v : {v // v ∈ paths i}) :
    ListVertexBlockIndex paths stride :=
  ⟨v.val,⟨(degreeGapPrefix (degreeGapArrivals paths v.val) (degreeReturnGapRank cuts v.val i)).card/stride,
    Nat.lt_succ_of_le (Nat.div_le_div_right (card_filter_le _ _))⟩⟩

/-- Place whole degree runs into blocks according to the occurrence
count at the start of each run. -/
noncomputable def packListVerticesAtDegreeGaps {n p : ℕ} (paths : Fin p → List (Fin n))
    (cuts : Fin n → Finset ℕ) (stride : ℕ) (i : Fin p) : List (ListVertexBlockIndex paths stride) :=
  (paths i).attach.map (packedDegreeReturnCopy paths cuts stride i)

theorem packListVerticesAtDegreeGaps_project {n p : ℕ} (paths : Fin p → List (Fin n))
    (cuts : Fin n → Finset ℕ) (stride : ℕ) (i : Fin p) :
    (packListVerticesAtDegreeGaps paths cuts stride i).map (·.fst) = paths i := by
  unfold packListVerticesAtDegreeGaps
  rw [List.map_map]
  exact List.attach_map_subtype_val _

private theorem packedDegreeReturnBlock_on {n p stride : ℕ}
    {paths : Fin p → List (Fin n)} {cuts : Fin n → Finset ℕ}
    {i : Fin p} {x : ListVertexBlockIndex paths stride}
    (on : x ∈ packListVerticesAtDegreeGaps paths cuts stride i) :
    x.fst ∈ paths i ∧ x.snd.val =
      (degreeGapPrefix (degreeGapArrivals paths x.fst) (degreeReturnGapRank cuts x.fst i)).card/stride := by
  obtain ⟨v,_,rfl⟩ := List.mem_map.mp on
  exact ⟨v.property,rfl⟩

private theorem occurrence_between_gap_and_run_end {p n : ℕ} (paths : Fin p → List (Fin n))
    (cuts : Fin n → Finset ℕ) {v : Fin n} {i : Fin p} {width : ℕ}
    (on : i ∈ degreeGapArrivals paths v)
    (run : ((degreeGapArrivals paths v).filter fun j =>
      degreeReturnGapRank cuts v j = degreeReturnGapRank cuts v i).card ≤ width) :
    (degreeGapPrefix (degreeGapArrivals paths v) (degreeReturnGapRank cuts v i)).card ≤
      (predecessors (degreeGapArrivals paths v) i).card ∧
    (predecessors (degreeGapArrivals paths v) i).card+1 ≤
      (degreeGapPrefix (degreeGapArrivals paths v) (degreeReturnGapRank cuts v i)).card+width := by
  let arrivals := degreeGapArrivals paths v
  let gap := degreeReturnGapRank cuts v i
  let shorter := degreeGapPrefix arrivals gap
  let inRun := arrivals.filter fun j => degreeReturnGapRank cuts v j = gap
  have less : gap ≤ i.val := degreeReturnGapRank_le_arrival cuts v i
  have lower : shorter ⊆ predecessors arrivals i := degreeGapPrefix_mono arrivals less
  have contained : insert i (predecessors arrivals i) ⊆ shorter ∪ inRun := by
    intro j here
    rcases mem_insert.mp here with rfl | earlier
    · exact mem_union.mpr (Or.inr (mem_filter.mpr ⟨on,rfl⟩))
    have jOn : j ∈ arrivals := (mem_filter.mp earlier).1
    have before : j < i := (mem_filter.mp earlier).2
    by_cases old : j.val < gap
    · exact mem_union.mpr (Or.inl (mem_filter.mpr ⟨jOn,old⟩))
    · have same := degreeReturnGapRank_eq_between cuts v before.le (le_of_not_gt old)
      exact mem_union.mpr (Or.inr (mem_filter.mpr ⟨jOn,same⟩))
  have fresh : i ∉ predecessors arrivals i := fun member => (lt_irrefl _) (mem_filter.mp member).2
  have upper := (card_le_card contained).trans ((card_union_le _ _).trans (Nat.add_le_add_left run shorter.card))
  rw [card_insert_of_notMem fresh] at upper
  exact ⟨card_le_card lower,upper⟩

set_option maxHeartbeats 1200000 in
private theorem packedDegreeReturn_degree {n p stride width : ℕ} (paths : Fin p → List (Fin n))
    (cuts : Fin n → Finset ℕ) (positive : 0 < stride)
    (run : ∀ v rank, ((degreeGapArrivals paths v).filter fun i =>
      degreeReturnGapRank cuts v i = rank).card ≤ width)
    (x : ListVertexBlockIndex paths stride) :
    (occurrences (fun i => (packListVerticesAtDegreeGaps paths cuts stride i).toFinset) x).card ≤ stride+width-1 := by
  let rank (i : Fin p) := (predecessors (degreeGapArrivals paths x.fst) i).card
  let marks (i : Fin p) := (packListVerticesAtDegreeGaps paths cuts stride i).toFinset
  let copies := occurrences marks x
  have incidence {i : Fin p} (on : i ∈ copies) : x ∈ packListVerticesAtDegreeGaps paths cuts stride i :=
    List.mem_toFinset.mp ((mem_occurrences (marks := marks)).mp on)
  let lowBound := stride*x.snd.val
  let highBound := lowBound+stride+width-1
  have original {i : Fin p} (on : i ∈ copies) : i ∈ degreeGapArrivals paths x.fst :=
    mem_occurrences.mpr (List.mem_toFinset.mpr (packedDegreeReturnBlock_on (incidence on)).1)
  have inside {i : Fin p} (on : i ∈ copies) : rank i ∈ Ico lowBound highBound := by
    obtain ⟨lower,upper⟩ := occurrence_between_gap_and_run_end paths cuts (original on)
      (run x.fst (degreeReturnGapRank cuts x.fst i))
    let first := (degreeGapPrefix (degreeGapArrivals paths x.fst) (degreeReturnGapRank cuts x.fst i)).card
    have fits : x.snd.val = first/stride := (packedDegreeReturnBlock_on (incidence on)).2
    have division := Nat.mod_add_div first stride
    have remainder := Nat.mod_lt first positive
    rw [← fits] at division
    change first ≤ rank i at lower
    change rank i+1 ≤ first+width at upper
    simp only [mem_Ico,lowBound,highBound]
    omega
  have eq : (Ico lowBound highBound).card ≤ stride+width-1 := by
    rw [Nat.card_Ico]
    dsimp only [highBound]
    omega
  exact (card_le_card_of_injOn rank (fun _ => inside)
    (fun _ h _ h' equal => predecessor_count_injective _ (original h) (original h') equal)).trans eq

/-- Packing the selected degree runs preserves mass and both upper
bounds for the copied alphabet. With half exclusion the gaps must be
safe whenever a short return could cross them backwards. -/
theorem packListVerticesAtDegreeGaps_spec {n p k : ℕ} {half : Bool}
    (paths : Fin p → List (Fin n)) (simple : ∀ i, (paths i).Nodup) (free : localOrderAdmissible half k paths)
    (cuts : Fin n → Finset ℕ)
    (safe : half = true → ∀ v gap, gap ∈ cuts v → IsSafeDegreeReturnGap paths v gap (k-3))
    (hn : 0 < n)
    (run : let M := ∑ i, (paths i).length
      ∀ v r, ((occurrences (fun i => (paths i).toFinset) v).filter
        fun j => degreeReturnGapRank cuts v j = r).card ≤ M/n) :
    let M := ∑ i, (paths i).length
    let stride := 3*M/n+1
    let rows := packListVerticesAtDegreeGaps paths cuts stride
    (∀ i, (rows i).Nodup) ∧ localOrderAdmissible half k rows ∧ (∑ i, (rows i).length) = M ∧
      3*Fintype.card (ListVertexBlockIndex paths stride) ≤ 4*n ∧
      ∀ w, (occurrences (fun i => (rows i).toFinset) w).card ≤ 4*M/n := by
  let M := ∑ i, (paths i).length
  let stride := 3*M/n+1
  let W := ListVertexBlockIndex paths stride
  let rows := packListVerticesAtDegreeGaps paths cuts stride
  let project (x : W) := x.fst
  let block (x : W) := x.snd.val
  have positive : 0 < stride := Nat.succ_pos _
  have labels {x y : W} (same : project x = project y) (rank : block x = block y) : x = y :=
    vertexBlock_eq_of_same_label same rank
  have sameRows (i : Fin p) : (rows i).map project = paths i :=
    packListVerticesAtDegreeGaps_project paths cuts stride i
  have mapSimple (i : Fin p) : ((rows i).map project).Nodup := (sameRows i).symm ▸ simple i
  have rowSimple (i : Fin p) : (rows i).Nodup := List.Nodup.of_map project (mapSimple i)
  have step {i x y} (edge : Before rows i x y) : Before paths i (project x) (project y) := by
    simpa only [sameRows] using listBefore_map project (mapSimple i) edge
  have blockMono {i j : Fin p} {x y : W}
      (left : x ∈ rows i) (right : y ∈ rows j) (same : project x = project y)
      (ordered : degreeReturnGapRank cuts (project x) i ≤ degreeReturnGapRank cuts (project x) j) :
      block x ≤ block y := by
    have first := (packedDegreeReturnBlock_on left).2
    have last := (packedDegreeReturnBlock_on right).2
    change block x = (degreeGapPrefix (degreeGapArrivals paths (project x)) _).card/stride at first
    change block y = (degreeGapPrefix (degreeGapArrivals paths (project y)) _).card/stride at last
    dsimp only [project] at first last same ordered
    rw [← same] at last
    rw [first,last]
    exact Nat.div_le_div_right (card_le_card (degreeGapPrefix_mono _ ordered))
  have copiedFree : localOrderAdmissible half k rows := by
    cases half
    · intro d size
      constructor
      intro bridge
      obtain ⟨j,bound,original,_⟩ := bridge.project_vertices project
        (fun {_ _ _} => step) (fun {_ _ _} => listBefore_ne)
      exact (free (k := j) (by omega)).false original
    · have allowed : NoShortBackwardProjection (Before rows) project block (k-3) := by
        apply NoShortBackwardProjection.of_safe_degree_return_gaps paths rows project block (fun {_ _ _} => step)
        intro a b x y s t first last same backwards
        have increasing := lt_of_not_ge (fun h =>
          backwards.not_ge (blockMono first.1 last.2.1 same h))
        have increasing' : degreeReturnGapRank cuts (project x) b < degreeReturnGapRank cuts (project x) a := increasing
        obtain ⟨gap,chosen,early,late⟩ := degreeReturnGapRank_lt_iff.mp increasing'
        exact ⟨gap,early,late,safe rfl (project x) gap chosen⟩
      have ordered {i j s t x y} (arrives : i ≤ j) (left : Before rows i s x) (right : Before rows j t y)
          (same : project x = project y) : block x ≤ block y :=
        blockMono left.2.1 right.2.1 same (degreeReturnGapRank_mono_arrival cuts (project x) arrives)
      exact HalfBridgeFree.of_noShortBackwardProjection free project block (fun {_ _} => labels)
        (fun {_ _ _} => step) (fun {_ _ _} => listBefore_ne) (fun {_ _ _ _ _ _} => ordered) allowed
  have bound : Fintype.card W ≤ n+M/stride := by
    have card := blockIndex_card_precise (degreeGapArrivals paths) positive
    have mass : (∑ v, (degreeGapArrivals paths v).card) = M := by
      change (∑ v, (occurrences (fun i => (paths i).toFinset) v).card) = _
      rw [sum_occurrences]
      exact sum_congr rfl (fun i _ => List.toFinset_card_of_nodup (simple i))
    simpa only [W,mass,Fintype.card_fin] using card
  have groups : 3*(M/stride) ≤ n := by
    have width := Nat.lt_mul_div_succ (3*M) hn
    change 3*M < n*stride at width
    apply Nat.le_of_mul_le_mul_right _ positive
    calc
      (3*(M/stride))*stride = 3*((M/stride)*stride) := by ring
      _ ≤ 3*M := Nat.mul_le_mul_left 3 (Nat.div_mul_le_self _ _)
      _ ≤ n*stride := width.le
  have copyCount : 3*Fintype.card W ≤ 4*n := by omega
  have degreeCap : stride+M/n-1 ≤ 4*M/n := by
    have product : ((3*M/n)+(M/n))*n ≤ 4*M := by
      rw [Nat.add_mul]
      have first := Nat.div_mul_le_self (3*M) n
      have next := Nat.div_mul_le_self M n
      omega
    have comparison : (3*M/n)+(M/n) ≤ 4*M/n := (Nat.le_div_iff_mul_le hn).mpr product
    change (3*M/n+1)+M/n-1 ≤ 4*M/n
    rw [Nat.add_right_comm _ 1 (M/n),Nat.add_sub_cancel]
    exact comparison
  have mass : (∑ i, (rows i).length) = M := sum_congr rfl (fun i _ => by
    rw [← sameRows i, List.length_map])
  exact ⟨rowSimple,copiedFree,mass,copyCount,fun w =>
    (packedDegreeReturn_degree paths cuts positive run w).trans degreeCap⟩

/-- At most one original mean degree per run allows the chosen safe gaps
to be packed within the original factor-four degree cap. -/
theorem regularization_list_frozen_half_of_small_degree_gap_runs {n p k : ℕ}
    (paths : Fin p → List (Fin n)) (simple : ∀ i, (paths i).Nodup) (free : HalfBridgeFree (Before paths) k)
    (cuts : Fin n → Finset ℕ) (safe : ∀ v gap, gap ∈ cuts v → IsSafeDegreeReturnGap paths v gap (k-3))
    (hn : 0 < n) (hp : 0 < p) (dense : n ≤ ∑ i, (paths i).length) (long : p ≤ ∑ i, (paths i).length)
    (run : let M := ∑ i, (paths i).length
      ∀ v r, ((occurrences (fun i => (paths i).toFinset) v).filter
        fun j => degreeReturnGapRank cuts v j = r).card ≤ M/n)
    (widthSafe : let M := ∑ i, (paths i).length
      NoShortReturnAcrossWidthCutsInPieces (packListVerticesAtDegreeGaps paths cuts (3*M/n+1)) (4*M/p) k) :
    let M := ∑ i, (paths i).length
    ∃ n' ≤ n, ∃ p' ≤ p, ∃ clean : Fin p' → List (Fin n'),
      (∀ i, (clean i).Nodup) ∧ HalfBridgeFree (Before clean) k ∧
      M ≤ 16*(∑ i, (clean i).length) ∧ (∑ i, (clean i).length) ≤ M ∧ frozenListCaps n p M clean := by
  obtain ⟨rowsSimple,rowsFree,mass,count,degree⟩ :=
    packListVerticesAtDegreeGaps_spec (half := true) paths simple free cuts (fun _ => safe) hn run
  exact regularization_list_frozen_of_safe_width_pieces (half := true) _ rowsSimple rowsFree widthSafe
    hn hp dense long count degree mass

/-- A chosen path gap forbids a short return across its cut in the full
precedence graph of the given rows. -/
def IsSafePathReturnGap {p : ℕ} {W : Type*} [LinearOrder W] [Fintype W] (rows : Fin p → List W) (i : Fin p) (gap radius : ℕ) : Prop :=
  ∀ ⦃x y⦄, Before rows i x y → (rows i).idxOf x < gap → gap ≤ (rows i).idxOf y →
    y ∉ reachIn (listPiecePrecedenceGraph rows) x radius

/-- The most recent chosen gap at this position on the row. -/
noncomputable def pathReturnGapRank {p : ℕ} {W : Type*} [LinearOrder W] (rows : Fin p → List W) (cuts : Fin p → Finset ℕ)
    (i : Fin p) (x : W) : ℕ :=
  degreeReturnGapRank cuts i
    (⟨(rows i).idxOf x,(List.idxOf_le_length).trans_lt (Nat.lt_succ_self _)⟩ : Fin ((rows i).length+1))

theorem pathReturnGapRank_lt_iff {p : ℕ} {W : Type*} [LinearOrder W] {rows : Fin p → List W} {cuts : Fin p → Finset ℕ}
    {i : Fin p} {x y : W} :
    pathReturnGapRank rows cuts i x < pathReturnGapRank rows cuts i y ↔
      ∃ gap ∈ cuts i, (rows i).idxOf x < gap ∧ gap ≤ (rows i).idxOf y :=
  degreeReturnGapRank_lt_iff

/-- Whole runs between chosen safe path gaps preserve the two budgets
and all four frozen caps when each run fits the original mean length. -/
theorem regularization_list_frozen_of_small_path_gap_runs {p n k M : ℕ} {W : Type*}
    [LinearOrder W] [Fintype W] {half : Bool}
    (rows : Fin p → List W) (simple : ∀ i, (rows i).Nodup) (allowed : localOrderAdmissible half k rows)
    (cuts : Fin p → Finset ℕ)
    (safe : ∀ i gap, gap ∈ cuts i → IsSafePathReturnGap rows i gap ((k-2)-1))
    (runs : ∀ i r, ((rows i).filter fun x => decide (pathReturnGapRank rows cuts i x = r)).length ≤ M/p)
    (hn : 0 < n) (hp : 0 < p) (dense : n ≤ M) (long : p ≤ M) (mass : (∑ i, (rows i).length) = M)
    (copyCount : 3*Fintype.card W ≤ 4*n)
    (degree : ∀ w, (occurrences (fun i => (rows i).toFinset) w).card ≤ 4*M/n) :
    ∃ n' ≤ n, ∃ p' ≤ p, ∃ clean : Fin p' → List (Fin n'),
      (∀ i, (clean i).Nodup) ∧ localOrderAdmissible half k clean ∧
      M ≤ 16*(∑ i, (clean i).length) ∧ (∑ i, (clean i).length) ≤ M ∧ frozenListCaps n p M clean := by
  refine regularization_list_frozen_of_small_ranked_path_runs rows simple allowed (pathReturnGapRank rows cuts)
    ?_ runs hn hp dense long mass copyCount degree
  intro i x y xMem yMem separated
  obtain ⟨gap,chosen,early,late⟩ := pathReturnGapRank_lt_iff.mp separated
  have step : Before rows i x y := ⟨xMem,yMem,early.trans_le late⟩
  exact ⟨step,safe i gap chosen step early late⟩

/-- Pack the degree and path runs in sequence. On each side one
original mean of incidences per run suffices for both frozen budgets. -/
theorem regularization_list_frozen_of_small_degree_and_path_gap_runs {n p k : ℕ} {half : Bool}
    (paths : Fin p → List (Fin n)) (simple : ∀ i, (paths i).Nodup) (free : localOrderAdmissible half k paths)
    (degreeCuts : Fin n → Finset ℕ) (pathCuts : Fin p → Finset ℕ)
    (degreeSafe : half = true → ∀ v gap, gap ∈ degreeCuts v → IsSafeDegreeReturnGap paths v gap (k-3))
    (degreeRuns : let M := ∑ i, (paths i).length
      ∀ v r, ((occurrences (fun i => (paths i).toFinset) v).filter
        fun j => degreeReturnGapRank degreeCuts v j = r).card ≤ M/n)
    (pathSafe : let M := ∑ i, (paths i).length
      let rows := packListVerticesAtDegreeGaps paths degreeCuts (3*M/n+1)
      ∀ i gap, gap ∈ pathCuts i → IsSafePathReturnGap rows i gap ((k-2)-1))
    (pathRuns : let M := ∑ i, (paths i).length
      let rows := packListVerticesAtDegreeGaps paths degreeCuts (3*M/n+1)
      ∀ i r, ((rows i).filter fun x => decide (pathReturnGapRank rows pathCuts i x = r)).length ≤ M/p)
    (hn : 0 < n) (hp : 0 < p) (dense : n ≤ ∑ i, (paths i).length) (long : p ≤ ∑ i, (paths i).length) :
    let M := ∑ i, (paths i).length
    ∃ n' ≤ n, ∃ p' ≤ p, ∃ clean : Fin p' → List (Fin n'),
      (∀ i, (clean i).Nodup) ∧ localOrderAdmissible half k clean ∧
      M ≤ 16*(∑ i, (clean i).length) ∧ (∑ i, (clean i).length) ≤ M ∧ frozenListCaps n p M clean := by
  obtain ⟨rowsSimple,rowsFree,mass,count,degree⟩ :=
    packListVerticesAtDegreeGaps_spec paths simple free degreeCuts degreeSafe hn degreeRuns
  exact regularization_list_frozen_of_small_path_gap_runs _ rowsSimple rowsFree pathCuts pathSafe pathRuns
    hn hp dense long mass count degree

/-- When each degree is below the packing stride, every incidence keeps
the zero copy label, regardless of the chosen degree gaps. -/
theorem packListVerticesAtDegreeGaps_eq_zero_block {n p stride : ℕ}
    (paths : Fin p → List (Fin n)) (cuts : Fin n → Finset ℕ)
    (small : ∀ v, (occurrences (fun i => (paths i).toFinset) v).card < stride) (i : Fin p) :
    packListVerticesAtDegreeGaps paths cuts stride i =
      (paths i).map (fun v => (⟨v,⟨0,Nat.succ_pos _⟩⟩ : ListVertexBlockIndex paths stride)) := by
  let embed (v : Fin n) : ListVertexBlockIndex paths stride := ⟨v,⟨0,Nat.succ_pos _⟩⟩
  change (paths i).attach.map (packedDegreeReturnCopy paths cuts stride i) = (paths i).map embed
  calc
    _ = (paths i).attach.map (fun v => embed v.val) := by
      apply List.map_congr_left
      intro v _
      refine vertexBlock_eq_of_same_label (u := packedDegreeReturnCopy paths cuts stride i v)
        (v := embed v.val) rfl ?_
      change (degreeGapPrefix (degreeGapArrivals paths v.val) (degreeReturnGapRank cuts v.val i)).card/stride = 0
      exact Nat.div_eq_of_lt ((card_filter_le _ _).trans_lt (small v.val))
    _ = ((paths i).attach.map Subtype.val).map embed := by simp only [List.map_map,Function.comp_def]
    _ = _ := by rw [List.attach_map_subtype_val]

end OnlineReachabilityPreservers
