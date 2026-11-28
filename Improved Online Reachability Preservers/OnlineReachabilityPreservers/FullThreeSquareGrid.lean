import OnlineReachabilityPreservers.FullThreeHexGridCleaning

/-! A degree-four full-three witness from both orientations of a square grid. -/

namespace OnlineReachabilityPreservers

open Finset
open scoped Prod.Lex
local notation "Before" => SourceAudit.BeforeIn

abbrev SignedSquarePoint (w : ℕ) := Fin w ×ₗ Fin w
abbrev SignedSquarePath (w : ℕ) := Bool ×ₗ (Bool ×ₗ Fin w)

private def squareX {w} (v : SignedSquarePoint w) : Fin w := (ofLex v).1
private def squareY {w} (v : SignedSquarePoint w) : Fin w := (ofLex v).2
private def squareVertical {w} (i : SignedSquarePath w) : Bool := (ofLex i).1
private def squareForward {w} (i : SignedSquarePath w) : Bool := (ofLex (ofLex i).2).1
private def squareLine {w} (i : SignedSquarePath w) : Fin w := (ofLex (ofLex i).2).2

private def squareAt {w} (i : SignedSquarePath w) (j : Fin w) : SignedSquarePoint w :=
  let changing := if squareForward i then j else j.rev
  if squareVertical i then toLex (squareLine i,changing) else toLex (changing,squareLine i)

/-- Each horizontal and vertical line is listed in both directions. -/
def signedSquareRows (w : ℕ) (i : SignedSquarePath w) : List (SignedSquarePoint w) := List.ofFn (squareAt i)

theorem signedSquareRows_length {w} (i : SignedSquarePath w) : (signedSquareRows w i).length = w := by
  simp [signedSquareRows]

theorem signedSquareRows_simple {w} (i : SignedSquarePath w) : (signedSquareRows w i).Nodup := by
  apply List.nodup_ofFn.mpr
  intro a b same
  cases axis : squareVertical i
  · have eq := congrArg squareX same
    cases dir : squareForward i <;> simp [squareAt,axis,dir,squareX] at eq
    all_goals exact eq
  · have eq := congrArg squareY same
    cases dir : squareForward i <;> simp [squareAt,axis,dir,squareY] at eq
    all_goals exact eq

private theorem squareRow_eq {w} {i j : SignedSquarePath w} (axis : squareVertical i = squareVertical j)
    (dir : squareForward i = squareForward j) (line : squareLine i = squareLine j) : i = j :=
  ofLex.injective (Prod.ext axis (ofLex.injective (Prod.ext dir line)))

private theorem square_no_three_on_line {w} {r a b : SignedSquarePath w}
    (axA : squareVertical r = squareVertical a) (axB : squareVertical r = squareVertical b)
    (lA : squareLine r = squareLine a) (lB : squareLine r = squareLine b) (ra : r ≠ a) (rb : r ≠ b) (ab : a ≠ b) : False := by
  cases hr : squareForward r <;> cases ha : squareForward a <;> cases hb : squareForward b
  all_goals first
    | exact ra (squareRow_eq axA (hr.trans ha.symm) lA)
    | exact rb (squareRow_eq axB (hr.trans hb.symm) lB)
    | exact ab (squareRow_eq (axA.symm.trans axB) (ha.trans hb.symm) (lA.symm.trans lB))

private theorem squareRows_index {w} (i : SignedSquarePath w) (j : Fin w) :
    @List.idxOf (SignedSquarePoint w) instBEqOfDecidableEq (squareAt i j) (signedSquareRows w i) = j.val := by
  let _ : BEq (SignedSquarePoint w) := instBEqOfDecidableEq
  have fits : j.val < (signedSquareRows w i).length := by rw [signedSquareRows_length]; exact j.isLt
  simpa [signedSquareRows] using (signedSquareRows_simple i).idxOf_getElem (i := j.val) fits

private theorem signedSquareRows_step {w} {i : SignedSquarePath w} {a b : SignedSquarePoint w}
    (step : Before (signedSquareRows w) i a b) :
    (squareVertical i = false ∧ squareY a = squareLine i ∧ squareY b = squareLine i ∧
      squareX a ≠ squareX b ∧ (squareForward i = true ↔ squareX a < squareX b)) ∨
    (squareVertical i = true ∧ squareX a = squareLine i ∧ squareX b = squareLine i ∧
      squareY a ≠ squareY b ∧ (squareForward i = true ↔ squareY a < squareY b)) := by
  obtain ⟨j,rfl⟩ := List.mem_ofFn.mp step.1
  obtain ⟨k,rfl⟩ := List.mem_ofFn.mp step.2.1
  have earlier := step.2.2
  rw [squareRows_index,squareRows_index] at earlier
  have inc : j < k := earlier
  cases axis : squareVertical i
  · left
    cases dir : squareForward i
    · have rev : k.rev < j.rev := by simpa using inc
      simp [squareAt,axis,dir,squareX,squareY,rev.ne.symm,not_lt_of_ge rev.le]
    · simp [squareAt,axis,dir,squareX,squareY,inc.ne,inc]
  · right
    cases dir : squareForward i
    · have rev : k.rev < j.rev := by simpa using inc
      simp [squareAt,axis,dir,squareX,squareY,rev.ne.symm,not_lt_of_ge rev.le]
    · simp [squareAt,axis,dir,squareX,squareY,inc.ne,inc]

/-- A one-step detour determines the same line and orientation. In a
two-step detour, both steps would have to lie on the river's line, which
has only two directions in total. -/
theorem signedSquareRows_full_three (w : ℕ) : BridgeFree (Before (signedSquareRows w)) 3 := by
  intro d small
  refine ⟨fun b => ?_⟩
  have cases : d = 0 ∨ d = 1 := by omega
  rcases cases with rfl | rfl
  · have river : Before (signedSquareRows w) b.river (b.vertex 0) (b.vertex 1) := b.riverStep
    have arc : Before (signedSquareRows w) (b.arc 0) (b.vertex 0) (b.vertex 1) := b.arcStep 0
    rcases signedSquareRows_step river with ⟨rA,r0,r1,rNe,rF⟩ | ⟨rA,r0,r1,rNe,rF⟩ <;>
      rcases signedSquareRows_step arc with ⟨aA,a0,a1,aNe,aF⟩ | ⟨aA,a0,a1,aNe,aF⟩
    all_goals first
      | exact rNe (a0.trans a1.symm)
      | apply b.river_ne_arc 0
        have signs : squareForward b.river = squareForward (b.arc 0) := by
          cases r : squareForward b.river <;> cases a : squareForward (b.arc 0) <;> simp_all
          all_goals omega
        exact squareRow_eq (rA.trans aA.symm) signs (r0.symm.trans a0)
  · have river : Before (signedSquareRows w) b.river (b.vertex 0) (b.vertex 2) := b.riverStep
    have first : Before (signedSquareRows w) (b.arc 0) (b.vertex 0) (b.vertex 1) := b.arcStep 0
    have last : Before (signedSquareRows w) (b.arc 1) (b.vertex 1) (b.vertex 2) := b.arcStep 1
    have ab : b.arc 0 ≠ b.arc 1 := b.distinctArcs.ne (by decide)
    rcases signedSquareRows_step river with ⟨rA,r0,r2,rNe,rF⟩ | ⟨rA,r0,r2,rNe,rF⟩ <;>
      rcases signedSquareRows_step first with ⟨aA,a0,a1,aNe,aF⟩ | ⟨aA,a0,a1,aNe,aF⟩ <;>
      rcases signedSquareRows_step last with ⟨cA,c1,c2,cNe,cF⟩ | ⟨cA,c1,c2,cNe,cF⟩
    all_goals first
      | exact square_no_three_on_line (rA.trans aA.symm) (rA.trans cA.symm) (r0.symm.trans a0)
          (r2.symm.trans c2) (b.river_ne_arc 0) (b.river_ne_arc 1) ab
      | omega

private def signedSquareFourBridge (vertical forward : Bool) (line : Fin 2) :
    Bridge (Before (signedSquareRows 2)) 2 := by
  let row (axis positive : Bool) (atLine : Fin 2) : SignedSquarePath 2 := toLex (axis,toLex (positive,atLine))
  let river := row vertical forward line
  let start := squareAt river 0
  let finish := squareAt river 1
  let other (v : SignedSquarePoint 2) :=
    if vertical then toLex (line.rev,squareY v) else toLex (squareX v,line.rev)
  let atSide (v : SignedSquarePoint 2) := if vertical then squareY v else squareX v
  let goesOut := decide (line = 0)
  refine ⟨![start,other start,other finish,finish],
    ![row (!vertical) goesOut (atSide start),row vertical forward line.rev,
      row (!vertical) (!goesOut) (atSide finish)],river,?_,?_,?_,?_,?_⟩
  all_goals cases vertical <;> cases forward <;> fin_cases line <;>
    (try unfold SourceAudit.BeforeIn) <;> decide +kernel

/-- On the two-by-two square, every oriented side can be the river of a
four-bridge. Taking the latest side makes a half-four bridge in any order. -/
theorem signedSquareRows_two_any_order_has_half_four (arrive : Fin 8 ≃ SignedSquarePath 2) :
    ¬ HalfBridgeFree (Before (fun i => signedSquareRows 2 (arrive i))) 4 := by
  let latest := arrive (Fin.last 7)
  let b := signedSquareFourBridge (squareVertical latest) (squareForward latest) (squareLine latest)
  have asRiver : b.river = latest := squareRow_eq rfl rfl rfl
  let lifted : Bridge (Before (fun i => signedSquareRows 2 (arrive i))) 2 :=
    b.mapPaths arrive.symm arrive.symm.injective (fun i _ _ step => by
      simpa only [SourceAudit.BeforeIn,Equiv.apply_symm_apply] using step)
  have lastRiver : lifted.river = Fin.last 7 := by
    change arrive.symm b.river = Fin.last 7
    rw [asRiver]
    exact arrive.symm_apply_apply _
  intro free
  apply free (by decide : 2+2 ≤ 4) lifted
  apply lt_of_le_of_ne
  · rw [lastRiver]
    exact Fin.le_last _
  · exact (lifted.river_ne_arc _).symm

private theorem signedSquareRows_mem {w} {i : SignedSquarePath w} {v : SignedSquarePoint w} :
    v ∈ signedSquareRows w i ↔ (if squareVertical i then squareX v else squareY v) = squareLine i := by
  rw [signedSquareRows,List.mem_ofFn]
  cases a : squareVertical i <;> cases b : squareForward i <;> simp only [squareAt,a,b,Bool.false_eq_true,ite_true,ite_false]
  all_goals constructor
  all_goals first
    | rintro ⟨j,rfl⟩; rfl
    | intro fixed
      first
      | exact ⟨(squareX v).rev,ofLex.injective (Prod.ext (Fin.rev_rev _) fixed.symm)⟩
      | exact ⟨squareX v,ofLex.injective (Prod.ext rfl fixed.symm)⟩
      | exact ⟨(squareY v).rev,ofLex.injective (Prod.ext fixed.symm (Fin.rev_rev _))⟩
      | exact ⟨squareY v,ofLex.injective (Prod.ext fixed.symm rfl)⟩

theorem signedSquareRows_degree {w} (v : SignedSquarePoint w) :
    (occurrences (fun i => (signedSquareRows w i).toFinset) v).card = 4 := by
  let row : (Bool × Bool) ↪ SignedSquarePath w :=
    ⟨fun x => toLex (x.1,toLex (x.2,if x.1 then squareX v else squareY v)),
      fun a b same => Prod.ext (congrArg squareVertical same) (congrArg squareForward same)⟩
  have matching : occurrences (fun i => (signedSquareRows w i).toFinset) v = univ.map row := by
    ext i
    simp only [mem_occurrences,List.mem_toFinset,signedSquareRows_mem,mem_map,mem_univ,true_and]
    refine ⟨fun on => ⟨(squareVertical i,squareForward i),squareRow_eq rfl rfl on⟩,?_⟩
    rintro ⟨d,rfl⟩
    rfl
  rw [matching,card_map,card_univ,Fintype.card_prod,Fintype.card_bool]

theorem signedSquareRows_vertices (w : ℕ) : Fintype.card (SignedSquarePoint w) = w*w := by
  rw [Fintype.card_congr ofLex,Fintype.card_prod,Fintype.card_fin]

theorem signedSquareRows_paths (w : ℕ) : Fintype.card (SignedSquarePath w) = 4*w := by
  rw [Fintype.card_congr ofLex,Fintype.card_prod,Fintype.card_bool,Fintype.card_congr ofLex,
    Fintype.card_prod,Fintype.card_bool,Fintype.card_fin]
  omega

/-- Disjoint copies of the degree-four square meet the four starting
caps for an input with mass between eight and sixteen times the vertex count. -/
theorem frozen_cleaning_full_three_signed_square {n p M : ℕ} (hp : 0 < p) (order : p ≤ n)
    (dense : 8*n < M) (upper : M ≤ 16*n) (pairs : 40*n < p*p) :
    ∃ v ≤ n, ∃ q ≤ p, ∃ rows : Fin q → List (Fin v), Function.Injective rows ∧
      (∀ i, rows i ≠ [] ∧ (rows i).Nodup) ∧ BridgeFree (Before rows) 3 ∧
      M ≤ 8*(∑ i, (rows i).length) ∧ (∑ i, (rows i).length) ≤ M ∧ frozenListCaps n p M rows := by
  let w := (M+4*p-1)/(4*p)
  obtain ⟨positive,cover,rounding⟩ := quarterMean_ceiling hp (show 0 < M by omega)
  change 0 < w at positive
  change M ≤ (4*p)*w at cover
  change (4*p)*w ≤ M+4*p-1 at rounding
  have long : 2 ≤ w := by
    by_contra! short
    have max := Nat.mul_le_mul_left (4*p) (show w ≤ 1 by omega)
    omega
  have width : p*w ≤ 5*n := by
    rw [Nat.mul_assoc] at rounding
    omega
  have vertexFit : w*w ≤ n := by
    have squared := Nat.pow_le_pow_left width 2
    have product := Nat.mul_le_mul_left n pairs.le
    have raw : (w*w)*(p*p) ≤ n*(p*p) := by nlinarith only [squared,product,Nat.zero_le (n^2)]
    exact Nat.le_of_mul_le_mul_right raw (by positivity)
  have pathFit : 4*w ≤ p := by
    have raw : p*(4*w) ≤ p*p := by nlinarith only [width,pairs,Nat.zero_le n]
    exact Nat.le_of_mul_le_mul_left raw hp
  have hasRows : 0 < Fintype.card (SignedSquarePath w) := by rw [signedSquareRows_paths]; positivity
  refine frozen_cleaning_full_three_of_regular_copies (width := w) (signedSquareRows w) signedSquareRows_simple
    (signedSquareRows_full_three w) signedSquareRows_degree (fun i => ?_) long hasRows
    ((signedSquareRows_vertices w).trans_le vertexFit) ((signedSquareRows_paths w).trans_le pathFit)
    (by omega) upper cover (by omega)
  simp [signedSquareRows_length]

/-- The larger degree-four witness gives the original-average literal
full-three comparison throughout `p ≤ n` and `p(p-1) ≤ 208n`. -/
theorem localOrderDistinctExtremal_frozen_full_three_of_square_budget {n p : ℕ}
    (hp : 0 < p) (order : p ≤ n) (budget : p*p-p ≤ 208*n)
    (feasible : ∃ paths : Fin p → List (Fin n), Function.Injective paths ∧
      (∀ i, paths i ≠ [] ∧ (paths i).Nodup) ∧ HalfBridgeFree (Before paths) 3) :
    ∃ paths : Fin p → List (Fin n), Function.Injective paths ∧
      (∀ i, paths i ≠ [] ∧ (paths i).Nodup) ∧ HalfBridgeFree (Before paths) 3 ∧
      (∀ other : Fin p → List (Fin n), Function.Injective other →
        (∀ i, other i ≠ [] ∧ (other i).Nodup) → HalfBridgeFree (Before other) 3 →
          (∑ i, (other i).length) ≤ ∑ i, (paths i).length) ∧
      let M := ∑ i, (paths i).length
      ∃ v ≤ n, ∃ q ≤ p, ∃ rows : Fin q → List (Fin v), Function.Injective rows ∧
        (∀ i, rows i ≠ [] ∧ (rows i).Nodup) ∧ BridgeFree (Before rows) 3 ∧
        M ≤ 8*(∑ i, (rows i).length) ∧ (∑ i, (rows i).length) ≤ M ∧ frozenListCaps n p M rows := by
  obtain ⟨paths,distinct,valid,legal,maximal,dense,_⟩ := localOrderDistinctExtremal_isDense (k := 3) true hp feasible
  refine ⟨paths,distinct,valid,legal,maximal,?_⟩
  let M := ∑ i, (paths i).length
  have hn : 0 < n := hp.trans_le order
  by_cases low : M ≤ 8*n
  · have upper : M ≤ 8*max n p := by simpa [max_eq_left order] using low
    obtain ⟨v,vFit,q,qFit,rows,unique,well,free,lower,cap,caps⟩ :=
      regularization_literal_half_full_all_of_low_mass paths distinct valid legal (by decide) hn hp dense upper
    exact ⟨v,vFit,q,qFit,rows,unique,well,free 3,lower,cap,caps⟩
  have simple (i : Fin p) := (valid i).2
  have moment : M^2 ≤ n*(p*p-p+3*M) := listMass_square_le_halfThree_degree paths simple legal le_rfl
  have upper : M ≤ 16*n := mass_le_mul_of_quadratic hn (a := 16) (c := 13) (by decide)
    (moment.trans (Nat.mul_le_mul_left n (by omega)))
  have enough := half_three_dense_mass_requires_path_square hn le_rfl paths simple legal (lt_of_not_ge low)
  exact frozen_cleaning_full_three_signed_square hp order (lt_of_not_ge low) upper enough


private def squareWidenPoint {w W : ℕ} (fits : w ≤ W) (v : SignedSquarePoint w) :
    SignedSquarePoint W :=
  toLex (Fin.castLE fits (squareX v), Fin.castLE fits (squareY v))

private theorem squareWidenPoint_injective {w W : ℕ} (fits : w ≤ W) :
    Function.Injective (squareWidenPoint fits) := by
  intro a b eq
  apply ofLex.injective
  exact Prod.ext (Fin.castLE_injective fits (congrArg squareX eq))
    (Fin.castLE_injective fits (congrArg squareY eq))

private def squareWidenRow {w W : ℕ} (fits : w ≤ W) (i : SignedSquarePath w) :
    SignedSquarePath W :=
  toLex (squareVertical i, toLex (squareForward i, Fin.castLE fits (squareLine i)))

private theorem squareWidenRow_injective {w W : ℕ} (fits : w ≤ W) :
    Function.Injective (squareWidenRow fits) := by
  intro a b eq
  have axis : squareVertical a = squareVertical b := congrArg (@squareVertical W) eq
  have orientation : squareForward a = squareForward b := congrArg (@squareForward W) eq
  exact squareRow_eq axis orientation (Fin.castLE_injective fits (congrArg squareLine eq))

private def squareWidenIndex {w W : ℕ} (fits : w ≤ W) (i : SignedSquarePath w) (j : Fin w) :
    Fin W :=
  if squareForward i then Fin.castLE fits j else (Fin.castLE fits j.rev).rev

private theorem squareWidenIndex_strict {w W : ℕ} (fits : w ≤ W) (i : SignedSquarePath w) :
    StrictMono (squareWidenIndex fits i) := by
  intro j k lt
  unfold squareWidenIndex
  split
  · exact lt
  · exact Fin.rev_lt_rev.mpr (show (Fin.castLE fits k.rev) < Fin.castLE fits j.rev from
      Fin.rev_lt_rev.mpr lt)

private theorem squareAt_widen {w W : ℕ} (fits : w ≤ W) (i : SignedSquarePath w) (j : Fin w) :
    squareAt (squareWidenRow fits i) (squareWidenIndex fits i j) =
      squareWidenPoint fits (squareAt i j) := by
  unfold squareAt squareWidenIndex squareWidenPoint
  have axisEq : squareVertical (squareWidenRow fits i) = squareVertical i := rfl
  have forwardEq : squareForward (squareWidenRow fits i) = squareForward i := rfl
  have lineEq : squareLine (squareWidenRow fits i) = Fin.castLE fits (squareLine i) := rfl
  rw [axisEq,forwardEq,lineEq]
  cases a : squareVertical i <;> cases f : squareForward i <;>
    simp [squareX,squareY]

private theorem signedSquareRows_widen_step {w W : ℕ} (fits : w ≤ W)
    {i : SignedSquarePath w} {a b : SignedSquarePoint w}
    (step : Before (signedSquareRows w) i a b) :
    Before (signedSquareRows W) (squareWidenRow fits i) (squareWidenPoint fits a)
      (squareWidenPoint fits b) := by
  obtain ⟨j,rfl⟩ := List.mem_ofFn.mp step.1
  obtain ⟨k,rfl⟩ := List.mem_ofFn.mp step.2.1
  have earlier := step.2.2
  rw [squareRows_index,squareRows_index] at earlier
  unfold SourceAudit.BeforeIn
  rw [← squareAt_widen fits i j,← squareAt_widen fits i k]
  refine ⟨List.mem_ofFn.mpr ⟨_,rfl⟩,List.mem_ofFn.mpr ⟨_,rfl⟩,?_⟩
  rw [squareRows_index,squareRows_index]
  exact squareWidenIndex_strict fits i earlier

/-- Every ordering of a signed square of width at least two contains a
half-four bridge. Only the eight rows through the first two coordinates
are needed. -/
theorem signedSquareRows_any_order_has_half_four {w : ℕ} (wide : 2 ≤ w)
    {I : Type*} [LinearOrder I] (arrival : I ≃ SignedSquarePath w) :
    ¬ HalfBridgeFree (Before (fun i => signedSquareRows w (arrival i))) 4 := by
  let position := arrival.symm ∘ squareWidenRow wide
  let used := (univ : Finset (SignedSquarePath 2)).image position
  have present (r : SignedSquarePath 2) : position r ∈ used :=
    mem_image.mpr ⟨r,mem_univ r,rfl⟩
  have nonempty : used.Nonempty := ⟨_,present (toLex (false,toLex (false,0)))⟩
  obtain ⟨latest,_,asMax⟩ := mem_image.mp (max'_mem used nonempty)
  let b := signedSquareFourBridge (squareVertical latest) (squareForward latest) (squareLine latest)
  have asRiver : b.river = latest := squareRow_eq rfl rfl rfl
  let lifted : Bridge (Before (fun i => signedSquareRows w (arrival i))) 2 :=
    (b.mapVertices (squareWidenPoint wide) (squareWidenPoint_injective wide)
      (fun _ _ _ step => signedSquareRows_widen_step wide step)).mapPaths
      position (arrival.symm.injective.comp (squareWidenRow_injective wide))
      (fun i _ _ step => by
        simpa only [position,Function.comp_apply,SourceAudit.BeforeIn,Equiv.apply_symm_apply] using step)
  have riverMax : lifted.river = used.max' nonempty := by
    change position b.river = _
    rwa [asRiver]
  intro free
  apply free (by decide : 2+2 ≤ 4) lifted
  apply lt_of_le_of_ne
  · rw [riverMax]
    exact le_max' used _ (present _)
  · exact (lifted.river_ne_arc _).symm

end OnlineReachabilityPreservers
