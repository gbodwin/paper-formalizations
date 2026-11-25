import OnlineReachabilityPreservers.OfflineOrderedBlocks

/-! Coordinate triangles obstruct a bounded number of increasing blocks in one common order. -/

namespace OnlineReachabilityPreservers

open Finset

namespace CoordinateTriangles

abbrev Rows (d : ℕ) := Fin d → Fin 3
abbrev Vertices (d : ℕ) := Fin d × Rows d

variable {d : ℕ}

def previous (r : Rows d) (t : Fin d) : Rows d := Function.update r t (r t - 1)
def next (r : Rows d) (t : Fin d) : Rows d := Function.update r t (r t + 1)

private theorem pred_ne (a : Fin 3) : a - 1 ≠ a := by fin_cases a <;> decide
private theorem pred_pred_ne (a : Fin 3) : a - 1 - 1 ≠ a := by fin_cases a <;> decide
private theorem next_three (a : Fin 3) : a + 1 + 1 + 1 = a := by fin_cases a <;> decide

theorem next_previous (t : Fin d) (r : Rows d) : next (previous r t) t = r := by
  funext w
  by_cases same : w = t
  · subst w
    simp [next, previous]
  · simp [next, previous, Function.update_of_ne same]

theorem previous_next (t : Fin d) (r : Rows d) : previous (next r t) t = r := by
  funext w
  by_cases same : w = t
  · subst w
    simp [next, previous]
  · simp [next, previous, Function.update_of_ne same]

private theorem previous_ne (r : Rows d) (t : Fin d) : previous r t ≠ r := by
  intro equal
  exact pred_ne (r t) (by simpa [previous] using congrFun equal t)

private theorem previous_twice_ne (r : Rows d) (t : Fin d) : previous (previous r t) t ≠ r := by
  intro equal
  exact pred_pred_ne (r t) (by simpa [previous] using congrFun equal t)

private theorem previous_injective (t : Fin d) : Function.Injective (fun r => previous r t) := by
  intro r s eq
  exact (next_previous t r).symm.trans
    ((congrArg (fun row => next row t) eq).trans (next_previous t s))

private theorem next_thrice (r : Rows d) (t : Fin d) : next (next (next r t) t) t = r := by
  funext w
  by_cases same : w = t
  · subst w
    simp [next, next_three]
  · simp [next, Function.update_of_ne same]

def positionLayer (i : Fin (2*d)) : Fin d := ⟨i.val/2, by have := i.isLt; omega⟩

def pathVertex (r : Rows d) (i : Fin (2*d)) : Vertices d :=
  let t := positionLayer i
  (t, if i.val%2 = 0 then previous r t else r)

/-- Each coordinate contributes one directed step on its three-row block. -/
def paths (r : Rows d) : List (Vertices d) := List.ofFn (pathVertex r)

@[simp] theorem path_length (r : Rows d) : (paths r).length = 2*d := List.length_ofFn

theorem path_simple (r : Rows d) : (paths r).Nodup := by
  apply List.nodup_ofFn_ofInjective
  intro i j same
  have layer : positionLayer i = positionLayer j := congrArg Prod.fst same
  have divEq : i.val/2 = j.val/2 := congrArg Fin.val layer
  have snd := congrArg Prod.snd same
  simp only [pathVertex, layer] at snd
  by_cases left : i.val%2 = 0 <;> by_cases right : j.val%2 = 0
  · apply Fin.ext; omega
  · exact (previous_ne _ _ (by simpa only [left,right,ite_true,ite_false] using snd)).elim
  · exact (previous_ne _ _ (by simpa only [left,right,ite_true,ite_false] using snd.symm)).elim
  · apply Fin.ext; omega

private theorem position (r : Rows d) (i : Fin (2*d)) :
    @List.idxOf (Vertices d) instBEqOfDecidableEq (pathVertex r i) (paths r) = i.val := by
  let _ : BEq (Vertices d) := instBEqOfDecidableEq
  have fits : i.val < (paths r).length := by simpa only [path_length] using i.isLt
  have idx := (path_simple r).idxOf_getElem (i := i.val) fits
  simpa only [paths, List.getElem_ofFn] using idx

private theorem positions_of_before {r : Rows d} {u v : Vertices d}
    (h : SourceAudit.BeforeIn paths r u v) :
    ∃ i j : Fin (2*d), u = pathVertex r i ∧ v = pathVertex r j ∧ i.val < j.val := by
  obtain ⟨i, hi⟩ := (List.mem_ofFn' (pathVertex r) u).mp h.1
  obtain ⟨j, hj⟩ := (List.mem_ofFn' (pathVertex r) v).mp h.2.1
  let _ : BEq (Vertices d) := instBEqOfDecidableEq
  refine ⟨i,j,hi.symm,hj.symm,?_⟩
  calc
    i.val = (paths r).idxOf u := hi ▸ (position r i).symm
    _ < (paths r).idxOf v := h.2.2
    _ = j.val := hj ▸ position r j

private theorem step_layer {r : Rows d} {u v : Vertices d}
    (h : SourceAudit.BeforeIn paths r u v) : u.1 ≤ v.1 := by
  obtain ⟨i,j,rfl,rfl,before⟩ := positions_of_before h
  change i.val/2 ≤ j.val/2
  omega

private theorem step_in_layer {r : Rows d} {u v : Vertices d}
    (h : SourceAudit.BeforeIn paths r u v) (same : u.1 = v.1) :
    u.2 = previous r u.1 ∧ v.2 = r := by
  obtain ⟨i,j,rfl,rfl,before⟩ := positions_of_before h
  have divEq : i.val/2 = j.val/2 := congrArg Fin.val same
  have left : i.val%2 = 0 := by omega
  have right : j.val%2 ≠ 0 := by omega
  simp [pathVertex, left, right]

private theorem on_path {r : Rows d} {u : Vertices d} (on : u ∈ paths r) :
    u.2 = previous r u.1 ∨ u.2 = r := by
  obtain ⟨i, rfl⟩ := (List.mem_ofFn' (pathVertex r) u).mp on
  simp only [pathVertex]
  split <;> simp

private theorem on_path_coordinate {r : Rows d} {u : Vertices d} (on : u ∈ paths r)
    {t : Fin d} (other : t ≠ u.1) : u.2 t = r t := by
  rcases on_path on with old | current
  · rw [old]
    simp [previous, Function.update_of_ne other]
  · rw [current]

private theorem share_agrees {r s : Rows d} {u : Vertices d} (first : u ∈ paths r)
    (second : u ∈ paths s) {t : Fin d} (other : t ≠ u.1) : r t = s t :=
  (on_path_coordinate first other).symm.trans (on_path_coordinate second other)

/-- Two different rows can meet only at the single coordinate in which they differ. -/
theorem unique_intersection {r s : Rows d} (different : r ≠ s) {u v : Vertices d}
    (ur : u ∈ paths r) (us : u ∈ paths s) (vr : v ∈ paths r) (vs : v ∈ paths s) : u = v := by
  have layer : u.1 = v.1 := by
    by_contra! apart
    apply different
    funext t
    by_cases equal : t = u.1
    · exact share_agrees vr vs (equal.trans_ne apart)
    · exact share_agrees ur us equal
  rcases on_path ur with ru | ru <;> rcases on_path us with su | su
  · exact (different (previous_injective _ (ru.symm.trans su))).elim
  · rcases on_path vr with rv | rv <;> rcases on_path vs with sv | sv
    · exact (different (previous_injective _ (rv.symm.trans sv))).elim
    · exact Prod.ext layer (ru.trans ((congrArg (previous r) layer).trans rv.symm))
    · have cycle : previous (previous r u.1) u.1 = r := by rw [ru.symm.trans su, layer, ← sv, rv]
      exact (previous_twice_ne _ _ cycle).elim
    · exact (different (rv.symm.trans sv)).elim
  · rcases on_path vr with rv | rv <;> rcases on_path vs with sv | sv
    · exact (different (previous_injective _ (rv.symm.trans sv))).elim
    · have cycle : previous (previous s u.1) u.1 = s := by rw [su.symm.trans ru, layer, ← rv, sv]
      exact (previous_twice_ne _ _ cycle).elim
    · exact Prod.ext layer (ru.trans rv.symm)
    · exact (different (rv.symm.trans sv)).elim
  · exact (different (ru.symm.trans su)).elim

/-- A chain crossing to a higher coordinate cannot return to the same row
without using it. Within a coordinate, the three distinct steps form a cycle. -/
theorem fully_bridge_free (k : ℕ) : IsEmpty (Bridge (SourceAudit.BeforeIn (paths (d := d))) k) := by
  classical
  refine ⟨fun b => ?_⟩
  let layer (i : Fin (k+2)) := (b.vertex i).1
  let s := layer 0
  have mono : Monotone layer := Fin.monotone_iff_le_succ.mpr fun i => step_layer (b.arcStep i)
  have fromStart (i : Fin (k+2)) : s ≤ layer i := mono (Fin.zero_le i)
  by_cases same : s = layer (Fin.last (k+1))
  · let z : Fin (k+1) := 0
    have zStart : z.castSucc = 0 := rfl
    have sameFirst : layer z.castSucc = layer z.succ := by
      rw [zStart]
      exact le_antisymm (fromStart _) ((mono (Fin.le_last _)).trans_eq same.symm)
    have left := (step_in_layer b.riverStep same).1
    have right := (step_in_layer (b.arcStep z) sameFirst).1
    apply b.river_ne_arc z
    apply previous_injective s
    simpa only [zStart] using left.symm.trans (show (b.vertex 0).2 = _ by simpa only [zStart] using right)
  · let above := (Finset.univ : Finset (Fin (k+2))).filter (fun i => s < layer i)
    have endAbove : s < layer (Fin.last (k+1)) := lt_of_le_of_ne (fromStart _) same
    have found : above.Nonempty := ⟨_, mem_filter.mpr ⟨mem_univ _,endAbove⟩⟩
    let first := above.min' found
    have firstAbove : s < layer first := (mem_filter.mp (min'_mem above found)).2
    have positive : 0 < first.val := by
      by_contra no
      have value : first.val = 0 := by omega
      have equal : first = 0 := Fin.ext value
      exact (lt_irrefl s) (by simpa only [equal] using firstAbove)
    let exit : Fin (k+1) := ⟨first.val-1, by have := first.isLt; omega⟩
    have exitNext : exit.succ = first := Fin.ext (by change first.val-1+1 = first.val; omega)
    have exitAbove : s < layer exit.succ := exitNext.symm ▸ firstAbove
    have exitStart : layer exit.castSucc = s := by
      apply le_antisymm _ (fromStart _)
      apply le_of_not_gt
      intro high
      have minLE := min'_le above exit.castSucc (mem_filter.mpr ⟨mem_univ _,high⟩)
      change first.val ≤ first.val-1 at minLE
      omega
    have agreesOff (j : Fin (k+1)) (prior : j ≤ exit) (t : Fin d) (other : t ≠ s) :
        b.arc j t = b.river t := by
      revert prior
      induction j using Fin.induction with
      | zero =>
        intro _
        exact share_agrees (b.arcStep 0).1 b.riverStep.1 other
      | succ j ih =>
        intro ordered
        have step : j.castSucc < j.succ := Fin.castSucc_lt_succ
        have earlier : j.castSucc ≤ exit := step.le.trans ordered
        have within : layer j.succ.castSucc = s := by
          apply le_antisymm _ (fromStart _)
          exact (mono (show j.succ.castSucc ≤ exit.castSucc from ordered)).trans_eq exitStart
        have different : t ≠ layer j.succ.castSucc := by rwa [within]
        have sameValue : b.arc j.succ t = b.arc j.castSucc t :=
          share_agrees (b.arcStep j.succ).1 (b.arcStep j.castSucc).2.1 different
        exact sameValue.trans (ih earlier)
    have agreesAt (j : Fin (k+1)) (later : exit ≤ j) : b.arc j s = b.river s := by
      revert later
      induction j using Fin.reverseInduction with
      | last =>
        intro _
        exact share_agrees (b.arcStep (Fin.last k)).2.1 b.riverStep.2.1 endAbove.ne
      | cast j ih =>
        intro ordered
        have step : j.castSucc < j.succ := Fin.castSucc_lt_succ
        have later : exit ≤ j.succ := ordered.trans step.le
        have aboveJoin : s < layer j.castSucc.succ :=
          exitAbove.trans_le (mono (show exit.succ ≤ j.castSucc.succ from Nat.succ_le_succ ordered))
        have sameValue : b.arc j.castSucc s = b.arc j.succ s :=
          share_agrees (b.arcStep j.castSucc).2.1 (b.arcStep j.succ).1 aboveJoin.ne
        exact sameValue.trans (ih later)
    apply b.river_ne_arc exit
    symm
    funext t
    by_cases equal : t = s
    · exact equal.symm ▸ agreesAt exit le_rfl
    · exact agreesOff exit le_rfl t equal

def nextEquiv (t : Fin d) : Rows d ≃ Rows d where
  toFun r := next r t
  invFun r := previous r t
  left_inv := previous_next t
  right_inv := next_previous t

def layerDescent (number : Vertices d → ℕ) (r : Rows d) (t : Fin d) : ℕ :=
  if number (t,r) < number (t,previous r t) then 1 else 0

/-- The number of descending two-vertex steps, one tested at each coordinate. -/
def rowDescents (number : Vertices d → ℕ) (r : Rows d) : ℕ :=
  ∑ t : Fin d, layerDescent number r t

private theorem triangle_has_descent (number : Vertices d → ℕ) (unique : Function.Injective number)
    (r : Rows d) (t : Fin d) :
    1 ≤ layerDescent number r t + layerDescent number (next r t) t +
      layerDescent number (next (next r t) t) t := by
  have last : previous r t = next (next r t) t := by
    have follows := previous_next t (next (next r t) t)
    rw [next_thrice] at follows
    exact follows
  unfold layerDescent
  rw [previous_next, previous_next]
  by_cases first : number (t,r) < number (t,previous r t)
  · simp only [first, ite_true]
    omega
  by_cases second : number (t,next r t) < number (t,r)
  · simp [first, second]
  by_cases third : number (t,next (next r t) t) < number (t,next r t)
  · simp [first, second, third]
  have same : number (t,previous r t) = number (t,r) := le_antisymm (le_of_not_gt first)
    ((le_of_not_gt second).trans ((le_of_not_gt third).trans_eq (congrArg (fun row => number (t,row)) last.symm)))
  exact (previous_ne r t (congrArg Prod.snd (unique same))).elim

private theorem layer_descent_total (number : Vertices d → ℕ) (unique : Function.Injective number) (t : Fin d) :
    Fintype.card (Rows d) ≤ 3 * ∑ r : Rows d, layerDescent number r t := by
  have once : (∑ r : Rows d, layerDescent number (next r t) t) = ∑ r : Rows d, layerDescent number r t :=
    Equiv.sum_comp (nextEquiv t) (fun r => layerDescent number r t)
  have twice : (∑ r : Rows d, layerDescent number (next (next r t) t) t) =
      ∑ r : Rows d, layerDescent number r t :=
    Equiv.sum_comp ((nextEquiv t).trans (nextEquiv t)) (fun r => layerDescent number r t)
  calc
    Fintype.card (Rows d) = ∑ _ : Rows d, 1 := by simp
    _ ≤ ∑ r : Rows d, (layerDescent number r t + layerDescent number (next r t) t +
        layerDescent number (next (next r t) t) t) :=
      sum_le_sum fun r _ => triangle_has_descent number unique r t
    _ = 3 * ∑ r : Rows d, layerDescent number r t := by
      rw [sum_add_distrib, sum_add_distrib, once, twice]
      omega

/-- Every common vertex numbering forces at least d/3 descents on
some row, counting only the adjacent steps within the coordinate layers. -/
theorem some_row_many_descents (number : Vertices d → ℕ) (unique : Function.Injective number) :
    ∃ r : Rows d, d ≤ 3 * rowDescents number r := by
  classical
  obtain ⟨r,_,best⟩ := exists_max_image (univ : Finset (Rows d)) (rowDescents number) univ_nonempty
  refine ⟨r,?_⟩
  have total : d * Fintype.card (Rows d) ≤ 3 * ∑ r : Rows d, rowDescents number r := calc
    _ = ∑ _ : Fin d, Fintype.card (Rows d) := by simp
    _ ≤ ∑ t : Fin d, (3 * ∑ r : Rows d, layerDescent number r t) :=
      sum_le_sum fun t _ => layer_descent_total number unique t
    _ = _ := by rw [← mul_sum, sum_comm]; rfl
  have maximum : (∑ a : Rows d, rowDescents number a) ≤ Fintype.card (Rows d) * rowDescents number r := by
    calc
      _ ≤ ∑ _ : Rows d, rowDescents number r := sum_le_sum best
      _ = _ := by simp
  have compare : d * Fintype.card (Rows d) ≤ (3 * rowDescents number r) * Fintype.card (Rows d) :=
    total.trans ((Nat.mul_le_mul_left 3 maximum).trans_eq (by ring))
  exact Nat.le_of_mul_le_mul_right compare (Fintype.card_pos (α := Rows d))

private def blockBoundaries : List (List ℕ) → Finset ℕ
  | [] => ∅
  | [_] => ∅
  | first::rest::tail =>
    insert first.length ((blockBoundaries (rest::tail)).image (first.length + ·))

private theorem blockBoundaries_card (parts : List (List ℕ)) :
    (blockBoundaries parts).card ≤ parts.length-1 := by
  induction parts with
  | nil => simp [blockBoundaries]
  | cons p ps ih =>
    cases ps with
    | nil => simp [blockBoundaries]
    | cons q qs =>
      unfold blockBoundaries
      have atMost := card_insert_le p.length ((blockBoundaries (q::qs)).image (p.length + ·))
      have imageCap : ((blockBoundaries (q::qs)).image (p.length + ·)).card ≤ (q::qs).length-1 :=
        card_image_le.trans ih
      simp only [List.length_cons] at imageCap ⊢
      omega

private theorem boundary_of_descent (parts : List (List ℕ))
    (ordered : ∀ row ∈ parts, row.Pairwise (· < ·))
    (i : ℕ) (fits : i+1 < parts.flatten.length)
    (down : parts.flatten[i+1] < parts.flatten[i]'(by omega)) :
    i+1 ∈ blockBoundaries parts := by
  induction parts generalizing i with
  | nil => simp at fits
  | cons first rest ih =>
    simp only [List.flatten_cons] at fits down
    by_cases within : i+1 < first.length
    · have left : i < first.length := by omega
      have step := List.pairwise_iff_getElem.mp (ordered first (List.mem_cons_self)) i (i+1) left within
        (Nat.lt_succ_self _)
      rw [List.getElem_append_left within, List.getElem_append_left left] at down
      exact (not_lt_of_ge step.le down).elim
    · cases rest with
      | nil =>
        simp only [List.flatten_nil, List.append_nil] at fits
        exact (within fits).elim
      | cons p ps =>
        by_cases left : i < first.length
        · have atBoundary : i+1 = first.length := by omega
          simp [blockBoundaries, atBoundary]
        · have beforeLeft : first.length ≤ i := Nat.le_of_not_gt left
          have beforeRight : first.length ≤ i+1 := beforeLeft.trans (Nat.le_succ _)
          have indexNext : i+1-first.length = (i-first.length)+1 := by omega
          rw [List.getElem_append_right beforeRight, List.getElem_append_right beforeLeft] at down
          have restFits : (i-first.length)+1 < (p::ps).flatten.length := by
            simp only [List.length_append] at fits
            omega
          have restDown : (p::ps).flatten[(i-first.length)+1] <
              (p::ps).flatten[i-first.length]'(by omega) := by
            simpa only [indexNext] using down
          have contained := ih (fun row mem => ordered row (List.mem_cons_of_mem _ mem))
            (i-first.length) restFits restDown
          exact mem_insert_of_mem (mem_image.mpr ⟨_,contained,by omega⟩)

private theorem numbered_incoming (number : Vertices d → ℕ) (r : Rows d) (t : Fin d) :
    ((paths r).map number)[2*t.val]'(by simp only [List.length_map, path_length]; have := t.isLt; omega) =
      number (t,previous r t) := by
  let i : Fin (2*d) := ⟨2*t.val, by have := t.isLt; omega⟩
  simp only [List.getElem_map, paths, List.getElem_ofFn]
  change number (pathVertex r i) = _
  have layer : positionLayer i = t := Fin.ext (by change (2*t.val)/2 = t.val; omega)
  have even : i.val%2 = 0 := by change (2*t.val)%2=0; omega
  simp [pathVertex, layer, even]

private theorem numbered_outgoing (number : Vertices d → ℕ) (r : Rows d) (t : Fin d) :
    ((paths r).map number)[2*t.val+1]'(by simp only [List.length_map, path_length]; have := t.isLt; omega) =
      number (t,r) := by
  let i : Fin (2*d) := ⟨2*t.val+1, by have := t.isLt; omega⟩
  simp only [List.getElem_map, paths, List.getElem_ofFn]
  change number (pathVertex r i) = _
  have layer : positionLayer i = t := Fin.ext (by change (2*t.val+1)/2 = t.val; omega)
  have odd : i.val%2 ≠ 0 := by change (2*t.val+1)%2≠0; omega
  simp [pathVertex, layer, odd]

private theorem descents_le_boundaries (number : Vertices d → ℕ) (r : Rows d)
    (parts : List (List ℕ)) (whole : parts.flatten = (paths r).map number)
    (ordered : ∀ row ∈ parts, row.Pairwise (· < ·)) : rowDescents number r ≤ parts.length-1 := by
  let descents := univ.filter (fun t : Fin d => number (t,r) < number (t,previous r t))
  have count : descents.card = rowDescents number r := by
    rw [card_eq_sum_ones]
    simp only [descents, sum_filter, rowDescents, layerDescent]
  let boundary (t : Fin d) := 2*t.val+1
  have injective : Function.Injective boundary := by
    intro t s same
    apply Fin.ext
    change 2*t.val+1 = 2*s.val+1 at same
    omega
  have sub : descents.image boundary ⊆ blockBoundaries parts := by
    intro point present
    obtain ⟨t,on,rfl⟩ := mem_image.mp present
    have down := (mem_filter.mp on).2
    have fits : 2*t.val+1 < parts.flatten.length := by
      rw [whole,List.length_map,path_length]
      have := t.isLt
      omega
    have fallen : parts.flatten[2*t.val+1] < parts.flatten[2*t.val]'(by omega) := by
      simp only [whole, numbered_incoming, numbered_outgoing]
      exact down
    exact boundary_of_descent parts ordered (2*t.val) fits fallen
  calc
    rowDescents number r = (descents.image boundary).card :=
      count.symm.trans (card_image_of_injective descents injective).symm
    _ ≤ (blockBoundaries parts).card := card_le_card sub
    _ ≤ parts.length-1 := blockBoundaries_card parts

/-- If every row splits into increasing blocks in a common vertex numbering,
some row needs at least d/3 internal boundaries. -/
theorem required_blocks (number : Vertices d → ℕ) (unique : Function.Injective number)
    (parts : Rows d → List (List ℕ))
    (whole : ∀ r, (parts r).flatten = (paths r).map number)
    (ordered : ∀ r row, row ∈ parts r → row.Pairwise (· < ·)) :
    ∃ r : Rows d, d ≤ 3*((parts r).length-1) := by
  obtain ⟨r,many⟩ := some_row_many_descents number unique
  exact ⟨r,many.trans (Nat.mul_le_mul_left 3 (descents_le_boundaries number r (parts r) (whole r) (ordered r)))⟩

@[simp] theorem row_count (d : ℕ) : Fintype.card (Rows d) = 3^d := by
  simp [Rows]

@[simp] theorem vertex_count (d : ℕ) : Fintype.card (Vertices d) = d*3^d := by
  simp [Vertices, Fintype.card_prod]

theorem mass (d : ℕ) : (∑ r : Rows d, (paths r).length) = 2*Fintype.card (Vertices d) := by
  simp only [path_length, sum_const, card_univ, row_count, vertex_count, smul_eq_mul]
  ring

theorem indexed_bridge_free {p : ℕ} (index : Fin p ≃ Rows d) (k : ℕ) :
    IsEmpty (Bridge (SourceAudit.BeforeIn (fun i => paths (index i))) k) :=
  ⟨fun b => (fully_bridge_free (d := d) k).false
    (b.mapPaths index index.injective (fun _ _ _ step => step))⟩

/-- The coordinate rows survive opposite-intersection pruning in every arrival order. -/
theorem indexed_pruning_fixed {p : ℕ} (index : Fin p ≃ Rows d) :
    removeOppositeIntersections (fun i => paths (index i)) = (fun i => paths (index i)) := by
  let family (i : Fin p) := paths (index i)
  have simple (i : Fin p) : (family i).Nodup := path_simple _
  funext i
  change removeOppositeIntersections family i = family i
  have sub := removeOppositeIntersections_sublist family i
  have equal : (removeOppositeIntersections family i).toFinset = (family i).toFinset := by
    ext v
    rw [List.mem_toFinset, List.mem_toFinset, removeOppositeIntersections_mem]
    constructor
    · exact And.left
    · intro on
      refine ⟨on, ?_⟩
      rintro ⟨j, earlier, u, one, other⟩
      have back := removeOppositeIntersections_before simple other
      have different : index i ≠ index j := fun eq => earlier.ne (index.injective eq).symm
      have same := unique_intersection different one.1 back.2.1 one.2.1 back.1
      exact listBefore_ne one same
  have lengths := congrArg Finset.card equal
  rw [List.toFinset_card_of_nodup (sub.nodup (simple i)), List.toFinset_card_of_nodup (simple i)] at lengths
  exact sub.eq_of_length_le lengths.ge

/-- Even after pruning, some row needs at least d/3 internal boundaries in
any common numbering that partitions the rows into increasing blocks. -/
theorem indexed_pruned_required_blocks {p : ℕ} (index : Fin p ≃ Rows d)
    (number : Vertices d → ℕ) (unique : Function.Injective number)
    (parts : Fin p → List (List ℕ))
    (whole : ∀ i, (parts i).flatten =
      (removeOppositeIntersections (fun j => paths (index j)) i).map number)
    (ordered : ∀ i row, row ∈ parts i → row.Pairwise (· < ·)) :
    ∃ i : Fin p, d ≤ 3*((parts i).length-1) := by
  simp only [indexed_pruning_fixed] at whole
  obtain ⟨r,many⟩ := required_blocks number unique (fun r => parts (index.symm r))
    (fun r => by simpa only [Equiv.apply_symm_apply] using whole (index.symm r))
    (fun r => ordered (index.symm r))
  exact ⟨index.symm r, many⟩

/-- For example, four coordinates already rule out two increasing blocks
per row, even after pruning. Increasing the dimension defeats any fixed
block bound. Distinct simple rows meet in at most one vertex, and every
full bridge is excluded. -/
theorem exists_pruning_blocks_obstruction (d bound : ℕ) (positive : 0 < d) (wide : 3*(bound-1) < d) :
    ∃ family : Fin (3^d) → List (Vertices d),
      (∀ i, (family i).Nodup ∧ (family i).length = 2*d ∧ family i ≠ []) ∧
      (∀ {i j u v}, i ≠ j → u ∈ family i → u ∈ family j → v ∈ family i → v ∈ family j → u = v) ∧
      (∀ k, IsEmpty (Bridge (SourceAudit.BeforeIn family) k)) ∧
      removeOppositeIntersections family = family ∧
      ∀ (number : Vertices d → ℕ), Function.Injective number →
        ∀ (parts : Fin (3^d) → List (List ℕ)),
          (∀ i, (parts i).flatten = (removeOppositeIntersections family i).map number) →
          (∀ i row, row ∈ parts i → row.Pairwise (· < ·)) →
          ∃ i, bound < (parts i).length := by
  let index : Fin (3^d) ≃ Rows d := (finCongr (row_count d)).symm.trans (Fintype.equivFin _).symm
  let family (i : Fin (3^d)) := paths (index i)
  refine ⟨family, ?_, ?_, indexed_bridge_free index, indexed_pruning_fixed index, ?_⟩
  · intro i
    refine ⟨path_simple _, path_length _, ?_⟩
    intro empty
    have zero : (family i).length = 0 := congrArg List.length empty
    rw [show (family i).length = 2*d from path_length _] at zero
    omega
  · intro i j u v different ui uj vi vj
    exact unique_intersection (fun equal => different (index.injective equal)) ui uj vi vj
  · intro number injective parts whole ordered
    obtain ⟨i,many⟩ := indexed_pruned_required_blocks index number injective parts whole ordered
    refine ⟨i, ?_⟩
    by_contra! small
    have cap := Nat.mul_le_mul_left 3 (Nat.sub_le_sub_right small 1)
    omega

end CoordinateTriangles

end OnlineReachabilityPreservers
