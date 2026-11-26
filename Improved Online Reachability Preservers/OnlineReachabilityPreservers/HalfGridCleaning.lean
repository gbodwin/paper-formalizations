import OnlineReachabilityPreservers.FrozenUnbalancedBudgets
import OnlineReachabilityPreservers.ExtremalCopyBounds

/-! Grid witnesses for frozen cleaning in the half-bridge mode. -/

namespace OnlineReachabilityPreservers

open Finset

local notation "Before" => SourceAudit.BeforeIn

abbrev HalfGridPoint (w : ℕ) := Fin w ×ₗ Fin w
abbrev HalfGridPath (w : ℕ) := Fin 3 ×ₗ Fin w

private def gridX {w : ℕ} (v : HalfGridPoint w) : Fin w := (ofLex v).1
private def gridY {w : ℕ} (v : HalfGridPoint w) : Fin w := (ofLex v).2
private def gridDirection {w : ℕ} (i : HalfGridPath w) : Fin 3 := (ofLex i).1
private def gridLine {w : ℕ} (i : HalfGridPath w) : Fin w := (ofLex i).2

private def halfGridAt {w : ℕ} (i : HalfGridPath w) (j : Fin w) : HalfGridPoint w :=
  if gridDirection i = 0 then toLex (j,gridLine i)
  else if gridDirection i = 1 then toLex (gridLine i,j)
  else toLex (gridLine i,j.rev)

/-- Horizontal paths come before both vertical orientations. -/
def halfGridRows (w : ℕ) (i : HalfGridPath w) : List (HalfGridPoint w) :=
  List.ofFn (halfGridAt i)

private theorem halfGridAt_injective {w : ℕ} (i : HalfGridPath w) : Function.Injective (halfGridAt i) := by
  intro a b same
  unfold halfGridAt at same
  split at same
  · exact congrArg gridX same
  · split at same
    · exact congrArg gridY same
    · exact Fin.rev_injective (congrArg gridY same)

theorem halfGridRows_simple {w : ℕ} (i : HalfGridPath w) : (halfGridRows w i).Nodup :=
  List.nodup_ofFn.mpr (halfGridAt_injective i)

theorem halfGridRows_length {w : ℕ} (i : HalfGridPath w) : (halfGridRows w i).length = w := by
  simp [halfGridRows]

private theorem halfGridRows_index {w : ℕ} (i : HalfGridPath w) (j : Fin w) :
    @List.idxOf (HalfGridPoint w) instBEqOfDecidableEq (halfGridAt i j) (halfGridRows w i) = j.val := by
  let _ : BEq (HalfGridPoint w) := instBEqOfDecidableEq
  have inside : j.val < (halfGridRows w i).length := (halfGridRows_length i).symm ▸ j.isLt
  simpa [halfGridRows] using (halfGridRows_simple i).idxOf_getElem (i := j.val) inside

private theorem gridDirection_two {w : ℕ} (i : HalfGridPath w)
    (h : gridDirection i ≠ 0) (rise : gridDirection i ≠ 1) : gridDirection i = 2 := by
  have notZero : (gridDirection i).val ≠ 0 := fun same => h (Fin.ext same)
  have notOne : (gridDirection i).val ≠ 1 := fun same => rise (Fin.ext same)
  have limit := (gridDirection i).isLt
  exact Fin.ext (by change (gridDirection i).val = 2; omega)

private theorem halfGridRows_step {w : ℕ} {i : HalfGridPath w} {a b : HalfGridPoint w}
    (step : Before (halfGridRows w) i a b) :
    (gridDirection i = 0 ∧ gridY a = gridLine i ∧ gridY b = gridLine i ∧ gridX a < gridX b) ∨
    (gridDirection i = 1 ∧ gridX a = gridLine i ∧ gridX b = gridLine i ∧ gridY a < gridY b) ∨
    (gridDirection i = 2 ∧ gridX a = gridLine i ∧ gridX b = gridLine i ∧ gridY b < gridY a) := by
  obtain ⟨u,rfl⟩ := List.mem_ofFn.mp step.1
  obtain ⟨v,rfl⟩ := List.mem_ofFn.mp step.2.1
  have ordered := step.2.2
  rw [halfGridRows_index,halfGridRows_index] at ordered
  by_cases horizontal : gridDirection i = 0
  · left
    exact ⟨horizontal,by simp [halfGridAt,horizontal,gridY],
      by simp [halfGridAt,horizontal,gridY],by simpa [halfGridAt,horizontal,gridX] using ordered⟩
  by_cases ascending : gridDirection i = 1
  · right
    left
    exact ⟨ascending,by simp [halfGridAt,ascending,gridX],
      by simp [halfGridAt,ascending,gridX],
      by simpa [halfGridAt,horizontal,ascending,gridY] using ordered⟩
  right
  right
  exact ⟨gridDirection_two i horizontal ascending,by simp [halfGridAt,horizontal,ascending,gridX],
    by simp [halfGridAt,horizontal,ascending,gridX],
    by simpa [halfGridAt,horizontal,ascending,gridY] using ordered⟩

private theorem gridPath_eq {w : ℕ} {a b : HalfGridPath w} (d : gridDirection a = gridDirection b)
    (l : gridLine a = gridLine b) : a = b := ofLex.injective (Prod.ext d l)

/-- At every cutoff, a horizontal river has a later vertical last arc.
A vertical river can only use its own column, where the other direction
cannot reach its end. -/
theorem halfGridRows_halfFree (w k : ℕ) : HalfBridgeFree (Before (halfGridRows w)) k := by
  intro s _ b earlier
  rcases halfGridRows_step b.riverStep with ⟨d,yStart,yLast,_⟩ | vertical
  · let i := Fin.last s
    have atEnd : i.succ = Fin.last (s+1) := Fin.succ_last _
    rcases halfGridRows_step (b.arcStep i) with hor | up | down
    · obtain ⟨aDir,_,aLast,_⟩ := hor
      rw [atEnd] at aLast
      exact b.river_ne_arc i (gridPath_eq (d.trans aDir.symm) (yLast.symm.trans aLast))
    · have riverFirst : b.river < b.arc i := Prod.Lex.lt_iff.mpr (Or.inl (by
        change gridDirection b.river < gridDirection (b.arc i)
        rw [d,up.1]
        decide))
      exact earlier.asymm riverFirst
    · have riverFirst : b.river < b.arc i := Prod.Lex.lt_iff.mpr (Or.inl (by
        change gridDirection b.river < gridDirection (b.arc i)
        rw [d,down.1]
        decide))
      exact earlier.asymm riverFirst
  · have xStart : gridX (b.vertex 0) = gridLine b.river := vertical.elim (fun h => h.2.1) (fun h => h.2.1)
    have xLast : gridX (b.vertex (Fin.last (s+1))) = gridLine b.river :=
      vertical.elim (fun h => h.2.2.1) (fun h => h.2.2.1)
    have nondecreasing : Monotone (fun j => gridX (b.vertex j)) := by
      apply Fin.monotone_iff_le_succ.mpr
      intro i
      rcases halfGridRows_step (b.arcStep i) with ⟨_,_,_,grow⟩ | ⟨_,same₁,same₂,_⟩ | ⟨_,same₁,same₂,_⟩
      · exact grow.le
      · exact (same₁.trans same₂.symm).le
      · exact (same₁.trans same₂.symm).le
    have sameColumn (j : Fin (s+2)) : gridX (b.vertex j) = gridLine b.river := by
      have left := nondecreasing (Fin.zero_le j)
      have right := nondecreasing (Fin.le_last j)
      exact le_antisymm (right.trans_eq xLast) (xStart.symm.trans_le left)
    have onlyVertical (i : Fin (s+1)) :
        gridLine (b.arc i) = gridLine b.river ∧
          ((gridDirection (b.arc i) = 1 ∧ gridY (b.vertex i.castSucc) < gridY (b.vertex i.succ)) ∨
           (gridDirection (b.arc i) = 2 ∧ gridY (b.vertex i.succ) < gridY (b.vertex i.castSucc))) := by
      rcases halfGridRows_step (b.arcStep i) with ⟨_,_,_,grow⟩ | ⟨d,onColumn,_,grow⟩ | ⟨d,onColumn,_,fall⟩
      · rw [sameColumn,sameColumn] at grow
        exact (lt_irrefl _ grow).elim
      · exact ⟨onColumn.symm.trans (sameColumn _),Or.inl ⟨d,grow⟩⟩
      · exact ⟨onColumn.symm.trans (sameColumn _),Or.inr ⟨d,fall⟩⟩
    rcases vertical with ⟨d,_,_,rise⟩ | ⟨d,_,_,fall⟩
    · have antitone : Antitone (fun j => gridY (b.vertex j)) := by
        apply Fin.antitone_iff_succ_le.mpr
        intro i
        obtain ⟨col,⟨dir,_⟩ | ⟨_,step⟩⟩ := onlyVertical i
        · exact (b.river_ne_arc i (gridPath_eq (d.trans dir.symm) col.symm)).elim
        · exact step.le
      exact (not_lt_of_ge (antitone (Fin.zero_le _))) rise
    · have monotone : Monotone (fun j => gridY (b.vertex j)) := by
        apply Fin.monotone_iff_le_succ.mpr
        intro i
        obtain ⟨col,⟨_,step⟩ | ⟨dir,_⟩⟩ := onlyVertical i
        · exact step.le
        · exact (b.river_ne_arc i (gridPath_eq (d.trans dir.symm) col.symm)).elim
      exact (not_lt_of_ge (monotone (Fin.zero_le _))) fall

private theorem halfGridRows_mem {w : ℕ} {i : HalfGridPath w} {v : HalfGridPoint w} :
    v ∈ halfGridRows w i ↔
      (if gridDirection i = 0 then gridY v else gridX v) = gridLine i := by
  rw [halfGridRows, List.mem_ofFn]
  by_cases horizontal : gridDirection i = 0
  · simp only [halfGridAt, horizontal, ite_true]
    refine ⟨?_, fun equal => ⟨gridX v, ofLex.injective (Prod.ext rfl equal.symm)⟩⟩
    rintro ⟨_,rfl⟩
    rfl
  · simp only [halfGridAt, horizontal, ite_false]
    by_cases up : gridDirection i = 1
    · simp only [up, ite_true]
      refine ⟨?_, fun equal => ⟨gridY v, ofLex.injective (Prod.ext equal.symm rfl)⟩⟩
      rintro ⟨_,rfl⟩
      rfl
    · simp only [up, ite_false]
      refine ⟨?_, fun equal => ⟨(gridY v).rev, ofLex.injective (Prod.ext equal.symm (Fin.rev_rev _))⟩⟩
      rintro ⟨_,rfl⟩
      rfl

/-- Every grid point belongs to one horizontal row and both orientations
of its column. -/
theorem halfGridRows_degree {w : ℕ} (v : HalfGridPoint w) :
    (occurrences (fun i => (halfGridRows w i).toFinset) v).card = 3 := by
  let lineAt (d : Fin 3) := if d = 0 then gridY v else gridX v
  let embed : Fin 3 ↪ HalfGridPath w := ⟨fun d => toLex (d,lineAt d), fun _ _ eq => congrArg gridDirection eq⟩
  have onRows : occurrences (fun i => (halfGridRows w i).toFinset) v = (univ : Finset (Fin 3)).map embed := by
    ext i
    simp only [mem_occurrences,List.mem_toFinset,halfGridRows_mem,mem_map,mem_univ,true_and]
    refine ⟨fun equal => ⟨gridDirection i, gridPath_eq rfl equal⟩,?_⟩
    rintro ⟨_,rfl⟩
    rfl
  rw [onRows, card_map, card_univ, Fintype.card_fin]

/-- An integer ceiling for one quarter of the input average. -/
theorem quarterMean_ceiling {q M : ℕ} (hq : 0 < q) (hM : 0 < M) :
    let w := (M+4*q-1)/(4*q)
    0 < w ∧ M ≤ (4*q)*w ∧ (4*q)*w ≤ M+4*q-1 := by
  let w := (M+4*q-1)/(4*q)
  have divisor : 0 < 4*q := by positivity
  have positive : 0 < w := Nat.div_pos (by omega) divisor
  have covers : M ≤ (4*q)*w := by
    have raw := Nat.lt_mul_div_succ (M+4*q-1) divisor
    change M+4*q-1 < (4*q)*(w+1) at raw
    rw [Nat.mul_succ] at raw
    omega
  exact ⟨positive,covers,by simpa only [Nat.mul_comm] using Nat.div_mul_le_self (M+4*q-1) (4*q)⟩

private theorem halfGrid_frozen_dimensions {n p M : ℕ} (hp : 0 < p) (order : p ≤ n)
    (dense : 8*n < M) (upper : M ≤ 12*n) (room : 16*n ≤ p*p) :
    ∃ w t : ℕ, 0 < w ∧ t*(w*w) ≤ n ∧ t*(3*w) ≤ p ∧
      M ≤ 8*(3*(t*(w*w))) ∧ 3*(t*(w*w)) ≤ M ∧
      M ≤ (4*p)*w ∧ p*w ≤ 4*M := by
  let w := (M+4*p-1)/(4*p)
  let t := min (n/(w*w)) (p/(3*w))
  obtain ⟨wPos,cover,widthBound⟩ := quarterMean_ceiling hp (Nat.zero_lt_of_lt dense)
  have widthCap : p*w ≤ 4*n := by
    change (4*p)*w ≤ M+4*p-1 at widthBound
    rw [Nat.mul_assoc] at widthBound
    omega
  have budgetWidth : 4*w ≤ p := by
    apply Nat.le_of_mul_le_mul_right _ hp
    rw [show (4*w)*p = 4*(p*w) by ring]
    omega
  have budgetSquare : w*w ≤ n := by
    have raw := Nat.mul_le_mul_right w budgetWidth
    rw [Nat.mul_assoc] at raw
    omega
  have budgetLines : 3*w ≤ p := by omega
  have vertexFit : t*(w*w) ≤ n :=
    (Nat.mul_le_mul_right _ (min_le_left _ _)).trans (Nat.div_mul_le_self _ _)
  have pathFit : t*(3*w) ≤ p :=
    (Nat.mul_le_mul_right _ (min_le_right _ _)).trans (Nat.div_mul_le_self _ _)
  have enough : M ≤ 8*(3*(t*(w*w))) := by
    by_cases vertexSide : n/(w*w) ≤ p/(3*w)
    · have large := floorBlockMass (show 0 < w*w by positivity) budgetSquare
      have identity : t = n/(w*w) := min_eq_left vertexSide
      rw [← identity] at large
      omega
    · have large := floorBlockMass (show 0 < 3*w by positivity) budgetLines
      have identity : t = p/(3*w) := min_eq_right (le_of_not_ge vertexSide)
      rw [← identity] at large
      have scaled := Nat.mul_le_mul_right (4*w) large
      calc
        M ≤ (4*p)*w := cover
        _ = p*(4*w) := by ring
        _ ≤ (2*(t*(3*w)))*(4*w) := scaled
        _ = 8*(3*(t*(w*w))) := by ring
  exact ⟨w,t,wPos,vertexFit,pathFit,enough,by omega,cover,by omega⟩

private theorem halfGridCopies_degree {w t : ℕ} (v : HalfGridPoint w ×ₗ Fin t) :
    (occurrences (fun i => (disjointListFamilies (fun _ : Fin t => halfGridRows w) i).toFinset) v).card = 3 :=
  (disjointListFamilies_degree (fun _ : Fin t => halfGridRows w) v).trans (halfGridRows_degree _)

/-- For mass between eight and twelve times the larger vertex budget,
copies of a degree-three grid meet the four original-average caps and
exclude half-bridges of every size. -/
theorem frozen_cleaning_half_grid {n p M : ℕ} (hp : 0 < p) (order : p ≤ n)
    (dense : 8*n < M) (upper : M ≤ 12*n) (room : 16*n ≤ p*p) :
    ∃ n' ≤ n, ∃ p' ≤ p, ∃ clean : Fin p' → List (Fin n'),
      (∀ i, (clean i).Nodup) ∧ (∀ k, HalfBridgeFree (Before clean) k) ∧
      M ≤ 8*(∑ i, (clean i).length) ∧ (∑ i, (clean i).length) ≤ M ∧ frozenListCaps n p M clean := by
  obtain ⟨w,t,_,vFits,pFits,retained,high,lowLen,highLen⟩ :=
    halfGrid_frozen_dimensions hp order dense upper room
  let copies (_ : Fin t) := halfGridRows w
  let family := disjointListFamilies copies
  have simple : ∀ i, (family i).Nodup := disjointListFamilies_simple copies (fun _ => halfGridRows_simple)
  have legal (k : ℕ) : localOrderAdmissible true k family :=
    disjointListFamilies_admissible copies (fun _ => halfGridRows_simple) (fun _ => halfGridRows_halfFree w k)
  have points : Fintype.card (HalfGridPoint w) = w*w := by
    rw [← Fintype.card_congr (toLex : Fin w × Fin w ≃ HalfGridPoint w),Fintype.card_prod,Fintype.card_fin]
  have lines : Fintype.card (HalfGridPath w) = 3*w := by
    rw [← Fintype.card_congr (toLex : Fin 3 × Fin w ≃ HalfGridPath w),Fintype.card_prod]
    simp only [Fintype.card_fin]
  let N := Fintype.card (HalfGridPoint w ×ₗ Fin t)
  let P := Fintype.card (HalfGridPath w ×ₗ Fin t)
  have nCount : N = t*(w*w) := by
    unfold N
    rw [← Fintype.card_congr (toLex : HalfGridPoint w × Fin t ≃ HalfGridPoint w ×ₗ Fin t),
      Fintype.card_prod,points,Fintype.card_fin,Nat.mul_comm]
  have pCount : P = t*(3*w) := by
    unfold P
    rw [← Fintype.card_congr (toLex : HalfGridPath w × Fin t ≃ HalfGridPath w ×ₗ Fin t),
      Fintype.card_prod,lines,Fintype.card_fin,Nat.mul_comm]
  have size : (∑ i, (family i).length) = 3*(t*(w*w)) := by
    unfold family
    rw [disjointListFamilies_mass]
    simp [copies,halfGridRows_length,lines,Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm]
  let clean := relabelListPathsFin family
  obtain ⟨simple',_,mass,degree,length⟩ := relabelListPathsFin_spec family simple (legal 2)
  have legal' (k : ℕ) : HalfBridgeFree (Before clean) k :=
    (relabelListPathsFin_spec family simple (legal k)).2.1
  have hn := hp.trans_le order
  have nPos : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have pPos : (0 : ℝ) < p := Nat.cast_pos.mpr hp
  refine ⟨N,nCount.trans_le vFits,P,pCount.trans_le pFits,clean,simple',legal',?_,?_,?_,?_⟩
  · exact (congrArg (8*·) (mass.trans size)).symm ▸ retained
  · exact (mass.trans size).symm ▸ high
  · intro v
    rw [degree,halfGridCopies_degree]
    constructor
    · apply (div_le_iff₀ (by positivity : 0 < 4*(n:ℝ))).mpr
      exact_mod_cast (show M ≤ 3*(4*n) by omega)
    · exact (le_div_iff₀ nPos).mpr (by exact_mod_cast (show 3*n ≤ 4*M by omega))
  · intro i
    rw [length]
    have len : (family ((Fintype.orderIsoFinOfCardEq (HalfGridPath w ×ₗ Fin t) rfl) i)).length = w := by
      simp [family,disjointListFamilies,copies,halfGridRows_length]
    rw [len]
    constructor
    · apply (div_le_iff₀ (by positivity : 0 < 4*(p:ℝ))).mpr
      exact_mod_cast (show M ≤ w*(4*p) by simpa only [Nat.mul_comm] using lowLen)
    · apply (le_div_iff₀ pPos).mpr
      exact_mod_cast (show w*p ≤ 4*M by simpa only [Nat.mul_comm] using highLen)

/-- With the smaller path budget and the stated quadratic budget bound,
either a low-mass witness or the grid meets all four original caps. -/
theorem regularization_list_frozen_half_of_large_vertex_budget {n p k : ℕ}
    (paths : Fin p → List (Fin n)) (simple : ∀ i, (paths i).Nodup)
    (free : HalfBridgeFree (Before paths) k) (three : 3 ≤ k)
    (hp : 0 < p) (order : p ≤ n)
    (dense : n ≤ ∑ i, (paths i).length) (long : p ≤ ∑ i, (paths i).length)
    (budget : p*p-p ≤ 108*n) :
    let M := ∑ i, (paths i).length
    ∃ n' ≤ n, ∃ p' ≤ p, ∃ clean : Fin p' → List (Fin n'),
      (∀ i, (clean i).Nodup) ∧ (∀ j, HalfBridgeFree (Before clean) j) ∧
      M ≤ 8*(∑ i, (clean i).length) ∧ (∑ i, (clean i).length) ≤ M ∧ frozenListCaps n p M clean := by
  let M := ∑ i, (paths i).length
  have hn := hp.trans_le order
  by_cases low : M ≤ 8*n
  · obtain ⟨n',vn,p',pn,clean,nodup,legal,retain,cap,limits⟩ :=
      regularization_list_frozen_low_mass_at_cutoff n paths simple free (by omega) hn hp dense long
        (by simpa only [max_eq_left order] using low)
    have freeAll (j : ℕ) : HalfBridgeFree (Before clean) j := by
      intro r _ b _
      have size : r+2 ≤ n' := by
        simpa only [Fintype.card_fin] using Fintype.card_le_of_injective b.vertex b.distinctVertices
      exact (legal (size.trans vn)).false b
    exact ⟨n',vn,p',pn,clean,nodup,freeAll,retain,cap,limits⟩
  have moment : M^2 ≤ n*(p*p-p+3*M) := listMass_square_le_halfThree_degree paths simple free three
  have upper : M ≤ 12*n := mass_le_mul_of_quadratic hn (a := 12) (c := 9) (by decide)
    (moment.trans (Nat.mul_le_mul_left n (by omega)))
  have room : 16*n ≤ p*p := by
    by_contra! small
    exact low (mass_le_mul_of_quadratic hn (a := 8) (c := 5) (by decide)
      (moment.trans (Nat.mul_le_mul_left n (by omega))))
  obtain ⟨n',vn,p',pn,clean,nodup,legal,retain,cap,limits⟩ :=
    frozen_cleaning_half_grid hp order (lt_of_not_ge low) upper room
  exact ⟨n',vn,p',pn,clean,nodup,legal,retain,cap,limits⟩

/-- The grid extends the original-cap result to the unrestricted half-bridge
maximum when p ≤ n and p(p−1) ≤ 108n. -/
theorem localOrderExtremal_frozen_half_of_large_vertex_budget (n p k : ℕ)
    (three : 3 ≤ k) (hp : 0 < p) (order : p ≤ n) (budget : p*p-p ≤ 108*n) :
    ∃ paths : Fin p → List (Fin n), (∀ i, (paths i).Nodup) ∧ HalfBridgeFree (Before paths) k ∧
      (∀ other : Fin p → List (Fin n), (∀ i, (other i).Nodup) →
        HalfBridgeFree (Before other) k → (∑ i, (other i).length) ≤ ∑ i, (paths i).length) ∧
      let M := ∑ i, (paths i).length
      ∃ n' ≤ n, ∃ p' ≤ p, ∃ clean : Fin p' → List (Fin n'),
        (∀ i, (clean i).Nodup) ∧ (∀ j, HalfBridgeFree (Before clean) j) ∧
        M ≤ 8*(∑ i, (clean i).length) ∧ (∑ i, (clean i).length) ≤ M ∧ frozenListCaps n p M clean := by
  obtain ⟨paths,simple,free,maximal,dense,long⟩ := localOrderExtremal_isDense n p k true (hp.trans_le order) hp
  exact ⟨paths,simple,free,maximal,
    regularization_list_frozen_half_of_large_vertex_budget paths simple free three hp order dense long budget⟩

end OnlineReachabilityPreservers
