import Mathlib.Data.Fin.VecNotation
import OnlineReachabilityPreservers.CyclicIntersections
import OnlineReachabilityPreservers.StrongAdversary

/-! The earlier-arc condition in Bridge Girth and the earlier last-arc
condition of Improved Online Reachability Preservers differ on the lattice. -/

namespace OnlineReachabilityPreservers

local notation "Before" => SourceAudit.BeforeIn

variable {steps rows slopes starts : ℕ}

/-- Read each lattice line in increasing layer order. The line indices
are ordered by slope and then by starting row. -/
def orderedLatticeRows (fits : LatticeFits steps rows slopes starts)
    (line : LatticeLine slopes starts) : List (LayerGrid steps rows) :=
  List.ofFn (latticeVertex fits line)

theorem orderedLatticeRows_simple (fits : LatticeFits steps rows slopes starts)
    (line : LatticeLine slopes starts) : (orderedLatticeRows fits line).Nodup :=
  List.nodup_ofFn.mpr (fun _ _ same => congrArg Prod.fst same)

private theorem orderedLatticeRows_index {fits : LatticeFits steps rows slopes starts}
    {line : LatticeLine slopes starts} {v : LayerGrid steps rows} (h : v ∈ orderedLatticeRows fits line) :
    let : BEq (LayerGrid steps rows) := instBEqOfDecidableEq
    (orderedLatticeRows fits line).idxOf v = v.1.val := by
  let : BEq (LayerGrid steps rows) := instBEqOfDecidableEq
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp h
  have inBounds : i.val < (orderedLatticeRows fits line).length := by
    simpa only [orderedLatticeRows,List.length_ofFn] using i.isLt
  have atIndex : (orderedLatticeRows fits line)[i.val]'inBounds = latticeVertex fits line i :=
    List.getElem_ofFn inBounds
  change (orderedLatticeRows fits line).idxOf (latticeVertex fits line i) = i.val
  rw [← atIndex,(orderedLatticeRows_simple fits line).idxOf_getElem]

private theorem orderedLatticeRows_height {fits : LatticeFits steps rows slopes starts}
    {line : LatticeLine slopes starts} {v : LayerGrid steps rows} (h : v ∈ orderedLatticeRows fits line) :
    (v.2.val : ℤ) = (ofLex line).2.val + (v.1.val : ℤ) * (ofLex line).1.val := by
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp h
  simp only [latticeVertex,Nat.cast_add,Nat.cast_mul]

/-- The slope-ordered lattice excludes bridges whose river arrives
after every arc, the condition of Bridge Girth, Definitions 9–10. -/
theorem orderedLatticeRows_no_bridge_with_all_arcs_earlier
    (fits : LatticeFits steps rows slopes starts) {d : ℕ}
    (b : Bridge (Before (orderedLatticeRows fits)) d) :
    ¬ ∀ i, b.arc i < b.river := by
  intro earlier
  let w : ℤ := (ofLex b.river).1.val
  let key (v : LayerGrid steps rows) : ℤ := (v.2.val : ℤ) - (v.1.val : ℤ)*w
  have difference {line : LatticeLine slopes starts} {x y : LayerGrid steps rows}
      (step : Before (orderedLatticeRows fits) line x y) :
      key y - key x = ((y.1.val : ℤ) - x.1.val)*((ofLex line).1.val-w) := by
    dsimp only [key]
    rw [orderedLatticeRows_height step.1,orderedLatticeRows_height step.2.1]
    ring
  have positive {line : LatticeLine slopes starts} {x y : LayerGrid steps rows}
      (step : Before (orderedLatticeRows fits) line x y) : 0 < (y.1.val : ℤ)-x.1.val := by
    let : BEq (LayerGrid steps rows) := instBEqOfDecidableEq
    have order : (orderedLatticeRows fits line).idxOf x < (orderedLatticeRows fits line).idxOf y := step.2.2
    have hx : (orderedLatticeRows fits line).idxOf x = x.1.val := orderedLatticeRows_index step.1
    have hy : (orderedLatticeRows fits line).idxOf y = y.1.val := orderedLatticeRows_index step.2.1
    rw [hx,hy] at order
    exact sub_pos.mpr (Int.ofNat_lt.mpr order)
  have slope (i : Fin (d+1)) : ((ofLex (b.arc i)).1.val : ℤ) ≤ w := by
    have compare := Prod.Lex.monotone_fst_ofLex (earlier i).le
    exact Int.ofNat_le.mpr compare
  have ordered : Antitone (key ∘ b.vertex) := by
    apply Fin.antitone_iff_succ_le.mpr
    intro i
    have loss := mul_nonpos_of_nonneg_of_nonpos (positive (b.arcStep i)).le (sub_nonpos.mpr (slope i))
    change key (b.vertex i.succ) ≤ key (b.vertex i.castSucc)
    linarith only [difference (b.arcStep i),loss]
  have ends : key (b.vertex (Fin.last (d+1))) = key (b.vertex 0) := by
    have eq := difference b.riverStep
    change _ = ((_ : ℤ)-_) * (w-w) at eq
    simp only [sub_self,mul_zero] at eq
    exact sub_eq_zero.mp eq
  let zeroArc : Fin (d+1) := 0
  have first := b.arcStep zeroArc
  have left : (zeroArc.castSucc : Fin (d+2)) = 0 := rfl
  have firstEnds : key (b.vertex zeroArc.succ) = key (b.vertex zeroArc.castSucc) := by
    apply le_antisymm (ordered (by simpa only [left] using (Fin.zero_le zeroArc.succ)))
    change key (b.vertex zeroArc.castSucc) ≤ key (b.vertex zeroArc.succ)
    rw [left,← ends]
    exact ordered (Fin.le_last _)
  have sameSlope : ((ofLex (b.arc zeroArc)).1.val : ℤ) = w := by
    have product := difference first
    rw [firstEnds,sub_self] at product
    rcases mul_eq_zero.mp product.symm with empty | equal
    · exact ((positive first).ne' empty).elim
    · exact sub_eq_zero.mp equal
  have sameStart : ((ofLex (b.arc zeroArc)).2.val : ℤ) = (ofLex b.river).2.val := by
    have startRiver := orderedLatticeRows_height b.riverStep.1
    have startArc := orderedLatticeRows_height first.1
    rw [left,sameSlope] at startArc
    change _ = _ + _*w at startRiver
    linarith only [startRiver,startArc]
  change ((ofLex (b.arc zeroArc)).1.val : ℤ) = (ofLex b.river).1.val at sameSlope
  apply b.river_ne_arc zeroArc
  apply ofLex.injective
  exact Prod.ext (Fin.ext (by exact_mod_cast sameSlope.symm)) (Fin.ext (by exact_mod_cast sameStart.symm))

private theorem orderedLatticeHalfThreeFits : LatticeFits 2 8 3 4 := by unfold LatticeFits; decide

private def orderedLatticeHalfThreeCorners : Fin 3 → LayerGrid 2 8 :=
  ![(0,1),(1,3),(2,3)]

private def orderedLatticeHalfThreeArcs : Fin 2 → LatticeLine 3 4 :=
  ![toLex (2,1),toLex (0,3)]

/-- On three layers, a slope-one river has a slope-two first arc and a
slope-zero last arc. The last arc is earlier than the river. -/
theorem orderedLatticeRows_half_three_example :
    ¬ HalfBridgeFree (Before (orderedLatticeRows orderedLatticeHalfThreeFits)) 3 := by
  let river : LatticeLine 3 4 := toLex (1,1)
  have distinctVertices : Function.Injective orderedLatticeHalfThreeCorners := by unfold Function.Injective; decide
  have distinctArcs : Function.Injective orderedLatticeHalfThreeArcs := by unfold Function.Injective; decide
  have different : ∀ i, river ≠ orderedLatticeHalfThreeArcs i := by decide
  have riverStep : Before (orderedLatticeRows orderedLatticeHalfThreeFits) river
      (orderedLatticeHalfThreeCorners 0) (orderedLatticeHalfThreeCorners (Fin.last 2)) := by
    unfold SourceAudit.BeforeIn
    decide
  have arcStep : ∀ i, Before (orderedLatticeRows orderedLatticeHalfThreeFits) (orderedLatticeHalfThreeArcs i)
      (orderedLatticeHalfThreeCorners i.castSucc) (orderedLatticeHalfThreeCorners i.succ) := by
    unfold SourceAudit.BeforeIn
    decide
  let bridge : Bridge (Before (orderedLatticeRows orderedLatticeHalfThreeFits)) 1 :=
    ⟨orderedLatticeHalfThreeCorners,orderedLatticeHalfThreeArcs,river,distinctVertices,distinctArcs,
      different,riverStep,arcStep⟩
  intro free
  exact free (k := 1) (by decide) bridge (by
    change (toLex ((0 : Fin 3),(3 : Fin 4))) < toLex (1,1)
    decide)

/-- The cited lattice condition does not imply half-bridge exclusion,
even for simple paths ordered by a common increasing layer coordinate. -/
theorem ordered_lattice_all_earlier_and_half_three_separate :
    ∃ paths : LatticeLine 3 4 → List (LayerGrid 2 8),
      (∀ i, (paths i).Nodup) ∧
      (∀ d (b : Bridge (Before paths) d), ¬ ∀ i, b.arc i < b.river) ∧
      ¬ HalfBridgeFree (Before paths) 3 := by
  refine ⟨orderedLatticeRows orderedLatticeHalfThreeFits,orderedLatticeRows_simple _,?_,
    orderedLatticeRows_half_three_example⟩
  exact fun _ b => orderedLatticeRows_no_bridge_with_all_arcs_earlier _ b

private theorem orderedLatticeRows_before_layers (fit : LatticeFits steps rows slopes starts)
    (line : LatticeLine slopes starts) {a b : Fin (steps+1)} (earlier : a < b) :
    Before (orderedLatticeRows fit) line (latticeVertex fit line a) (latticeVertex fit line b) := by
  have left : latticeVertex fit line a ∈ orderedLatticeRows fit line := List.mem_ofFn.mpr ⟨a,rfl⟩
  have right : latticeVertex fit line b ∈ orderedLatticeRows fit line := List.mem_ofFn.mpr ⟨b,rfl⟩
  refine ⟨left,right,?_⟩
  rw [orderedLatticeRows_index left,orderedLatticeRows_index right]
  exact earlier

/-- Four lines on the first three layers impose two opposite arrival
constraints at half cutoff three. Any arrival order on the complete
lattice fails once these four lines are present. -/
theorem orderedLatticeRows_no_half_three_reordering {J : Type*} [LinearOrder J]
    (fit : LatticeFits steps rows slopes starts) (depth : 2 ≤ steps)
    (slopeBudget : 4 ≤ slopes) (startBudget : 3 ≤ starts)
    (arrival : LatticeLine slopes starts ≃ J) :
    ¬ HalfBridgeFree (Before (fun j => orderedLatticeRows fit (arrival.symm j))) 3 := by
  let a : LatticeLine slopes starts := toLex (⟨1,by omega⟩,⟨2,by omega⟩)
  let b : LatticeLine slopes starts := toLex (⟨2,by omega⟩,⟨0,by omega⟩)
  let c : LatticeLine slopes starts := toLex (⟨0,by omega⟩,⟨2,by omega⟩)
  let d : LatticeLine slopes starts := toLex (⟨3,by omega⟩,⟨0,by omega⟩)
  let u : Fin (steps+1) := 0
  let v : Fin (steps+1) := ⟨1,by omega⟩
  let w : Fin (steps+1) := ⟨2,by omega⟩
  have uv : u < v := by change (0:ℕ) < 1; decide
  have vw : v < w := by change (1:ℕ) < 2; decide
  let point := latticeVertex fit
  have stepOn (line : LatticeLine slopes starts) {x y : Fin (steps+1)} (order : x < y) :
      Before (orderedLatticeRows fit) line (point line x) (point line y) :=
    orderedLatticeRows_before_layers fit line order
  have ca : point c u = point a u := Prod.ext rfl (Fin.ext rfl)
  have cb : point c v = point b v := Prod.ext rfl (Fin.ext rfl)
  have db : point d u = point b u := Prod.ext rfl (Fin.ext rfl)
  have da : point d v = point a v := Prod.ext rfl (Fin.ext rfl)
  have abPoint : point a w = point b w := Prod.ext rfl (Fin.ext rfl)
  have apart {x y : LatticeLine slopes starts}
      (different : (ofLex x).1.val ≠ (ofLex y).1.val) : x ≠ y :=
    fun same => different (congrArg (fun line => (ofLex line).1.val) same)
  have ab : a ≠ b := apart (by change (1:ℕ) ≠ 2; decide)
  have arcCA := stepOn c uv
  have arcDB := stepOn d uv
  rw [ca,cb] at arcCA
  rw [db,da] at arcDB
  have riverA := stepOn a (uv.trans vw)
  have riverB := stepOn b (uv.trans vw)
  rw [abPoint] at riverA
  rw [← abPoint] at riverB
  let aBridge := threeListBridge (apart (by change (0:ℕ) ≠ 2; decide))
    (apart (by change (1:ℕ) ≠ 0; decide)) ab arcCA
    (stepOn b vw) riverA
  let bBridge := threeListBridge (apart (by change (3:ℕ) ≠ 1; decide))
    (apart (by change (2:ℕ) ≠ 3; decide)) ab.symm arcDB
    (stepOn a vw) riverB
  let map (bridge : Bridge (Before (orderedLatticeRows fit)) 1) :
      Bridge (Before (fun j => orderedLatticeRows fit (arrival.symm j))) 1 :=
    bridge.mapPaths arrival arrival.injective (fun _ _ _ step => by
      simpa only [SourceAudit.BeforeIn,Equiv.symm_apply_apply] using step)
  intro free
  rcases lt_or_gt_of_ne (arrival.injective.ne ab) with aEarlier | bEarlier
  · exact free (k := 1) (by decide) (map bBridge) aEarlier
  · exact free (k := 1) (by decide) (map aBridge) bEarlier

end OnlineReachabilityPreservers
