import OnlineReachabilityPreservers.FullReturnRadius

/-! Sharpness examples for the return radius at all larger full cutoffs. -/

namespace OnlineReachabilityPreservers.SourceAudit

open Finset

private abbrev SharpVertex (extra : ℕ) := Fin (extra+7)

private def highCorner (extra : ℕ) : SharpVertex extra := ⟨extra+3, by omega⟩
private def nextCorner (extra : ℕ) : SharpVertex extra := ⟨extra+4, by omega⟩
private def terminal (extra : ℕ) : SharpVertex extra := Fin.last (extra+6)

def fullReturnSharpPieces (extra : ℕ) (i : SharpVertex extra) : List (SharpVertex extra) :=
  if i = terminal extra then [0, terminal extra] else [i,i+1]

def fullReturnSharpParent (extra : ℕ) (i : SharpVertex extra) : SharpVertex extra :=
  if i = highCorner extra then 0 else i

def fullReturnSharpRows (extra : ℕ) (i : SharpVertex extra) : List (SharpVertex extra) :=
  if i = 0 then [highCorner extra, nextCorner extra, 0, 1]
  else if i = highCorner extra then []
  else fullReturnSharpPieces extra i

private theorem different_of_values {n : ℕ} {x y : Fin n} (apart : x.val ≠ y.val) : x ≠ y :=
  fun equal => apart (congrArg Fin.val equal)

@[local simp] private theorem high_ne_zero {extra : ℕ} : highCorner extra ≠ 0 :=
  different_of_values (by change extra+3 ≠ 0; omega)

@[local simp] private theorem high_ne_one {extra : ℕ} : highCorner extra ≠ 1 :=
  different_of_values (by change extra+3 ≠ 1; omega)

@[local simp] private theorem next_ne_zero {extra : ℕ} : nextCorner extra ≠ 0 :=
  different_of_values (by change extra+4 ≠ 0; omega)

@[local simp] private theorem next_ne_one {extra : ℕ} : nextCorner extra ≠ 1 :=
  different_of_values (by change extra+4 ≠ 1; omega)

@[local simp] private theorem high_ne_next {extra : ℕ} : highCorner extra ≠ nextCorner extra :=
  different_of_values (by change extra+3 ≠ extra+4; omega)

@[local simp] private theorem terminal_ne_zero {extra : ℕ} : terminal extra ≠ 0 :=
  different_of_values (by change extra+6 ≠ 0; omega)

@[local simp] private theorem terminal_ne_high {extra : ℕ} : terminal extra ≠ highCorner extra :=
  different_of_values (by change extra+6 ≠ extra+3; omega)

private theorem successor_val {extra : ℕ} {i : SharpVertex extra} (before : i ≠ terminal extra) :
    (i+1).val = i.val+1 := by
  rw [Fin.val_add,Fin.val_one]
  apply Nat.mod_eq_of_lt
  have bound := i.isLt
  have notLast : i.val ≠ extra+6 := fun equal => before (Fin.ext equal)
  omega

private theorem successor_ne {extra : ℕ} {i : SharpVertex extra} (before : i ≠ terminal extra) : i ≠ i+1 :=
  different_of_values (by rw [successor_val before]; omega)

private theorem pair_step {I V : Type*} [DecidableEq V] {rows : I → List V} {i : I}
    {a b x y : V} (pair : rows i = [a,b]) (different : a ≠ b) :
    BeforeIn rows i x y ↔ x = a ∧ y = b := by
  unfold BeforeIn
  rw [pair]
  constructor
  · intro on
    have optionsX : x = a ∨ x = b := by simpa using on.1
    have optionsY : y = a ∨ y = b := by simpa using on.2.1
    rcases optionsX with rfl | rfl <;> rcases optionsY with rfl | rfl
    · exact (lt_irrefl _ on.2.2).elim
    · exact ⟨rfl,rfl⟩
    · have impossible := on.2.2
      simp [different] at impossible
    · exact (lt_irrefl _ on.2.2).elim
  · rintro ⟨rfl,rfl⟩
    simp [different, different.symm]

private theorem piece_step_shape {extra : ℕ} {i x y : SharpVertex extra}
    (step : BeforeIn (fullReturnSharpPieces extra) i x y) :
    (i = terminal extra ∧ x = 0 ∧ y = terminal extra) ∨
      (i ≠ terminal extra ∧ x = i ∧ y.val = x.val+1) := by
  by_cases final : i = terminal extra
  · exact Or.inl ⟨final, (pair_step (ite_eq_left final) terminal_ne_zero.symm).mp step⟩
  · obtain ⟨first,last⟩ := (pair_step (ite_eq_right final) (successor_ne final)).mp step
    exact Or.inr ⟨final,first,last.symm ▸ first.symm ▸ successor_val final⟩

private theorem long_step_shape {extra : ℕ} {x y : SharpVertex extra}
    (step : BeforeIn (fullReturnSharpRows extra) 0 x y) :
    (x = highCorner extra ∧ y = nextCorner extra) ∨
      ((x = highCorner extra ∨ x = nextCorner extra) ∧ (y = 0 ∨ y = 1)) ∨
      (x = 0 ∧ y = 1) := by
  have xCases : x = highCorner extra ∨ x = nextCorner extra ∨ x = 0 ∨ x = 1 :=
    by simpa [fullReturnSharpRows] using step.1
  have yCases : y = highCorner extra ∨ y = nextCorner extra ∨ y = 0 ∨ y = 1 :=
    by simpa [fullReturnSharpRows] using step.2.1
  rcases xCases with rfl | rfl | rfl | rfl <;> rcases yCases with rfl | rfl | rfl | rfl <;>
    first | (simp [Ne.symm]; done) | simp_all [BeforeIn, fullReturnSharpRows, Ne.symm]

private theorem original_step_shape {extra : ℕ} {i x y : SharpVertex extra}
    (step : BeforeIn (fullReturnSharpRows extra) i x y) :
    (i = 0 ∧ ((x = highCorner extra ∧ y = nextCorner extra) ∨
      ((x = highCorner extra ∨ x = nextCorner extra) ∧ (y = 0 ∨ y = 1)) ∨ (x = 0 ∧ y = 1))) ∨
    (i = terminal extra ∧ x = 0 ∧ y = terminal extra) ∨
    (i ≠ 0 ∧ i ≠ highCorner extra ∧ i ≠ terminal extra ∧ x = i ∧ y.val = x.val+1) := by
  by_cases first : i = 0
  · exact Or.inl ⟨first, long_step_shape (first ▸ step)⟩
  by_cases high : i = highCorner extra
  · have onRow := step.1
    rw [fullReturnSharpRows, ite_eq_right first, ite_eq_left high] at onRow
    exact (List.not_mem_nil onRow).elim
  have piece : BeforeIn (fullReturnSharpPieces extra) i x y := by
    unfold BeforeIn at step ⊢
    simpa only [fullReturnSharpRows, ite_eq_right first, ite_eq_right high] using step
  rcases piece_step_shape piece with river | ⟨last, start, finish⟩
  · exact Or.inr (Or.inl river)
  · exact Or.inr (Or.inr ⟨first,high,last,start,finish⟩)

private theorem unmerged_step_increases {extra : ℕ} {i x y : SharpVertex extra} (other : i ≠ 0)
    (step : BeforeIn (fullReturnSharpRows extra) i x y) : x.val < y.val := by
  rcases original_step_shape step with ⟨zero,_⟩ | ⟨_,start,last⟩ | ⟨_,_,_,_,moves⟩
  · exact (other zero).elim
  · rw [start,last]
    change 0 < extra+6
    omega
  · omega

private theorem dart_step {extra : ℕ} {i x y : SharpVertex extra} (unmerged : i ≠ 0)
    (notRiver : i ≠ terminal extra) (step : BeforeIn (fullReturnSharpRows extra) i x y) :
    i ≠ highCorner extra ∧ x = i ∧ y.val = x.val+1 := by
  rcases original_step_shape step with ⟨zero,_⟩ | ⟨last,_⟩ | ⟨_,high,_,start,move⟩
  · exact (unmerged zero).elim
  · exact (notRiver last).elim
  · exact ⟨high,start,move⟩

set_option maxHeartbeats 650000 in
/-- The merged family excludes full bridges at every cutoff. -/
theorem fullReturnSharpRows_fullFree (extra cutoff : ℕ) : BridgeFree (BeforeIn (fullReturnSharpRows extra)) cutoff := by
  intro d _
  refine ⟨fun b => ?_⟩
  let final := Fin.last (d+1)
  let endArc := Fin.last d
  have endStep : BeforeIn (fullReturnSharpRows extra) (b.arc endArc) (b.vertex endArc.castSucc) (b.vertex final) := by
    simpa only [final, endArc, Fin.succ_last] using b.arcStep endArc
  rcases original_step_shape b.riverStep with ⟨merged, comparison⟩ | ⟨river, start, finish⟩ |
    ⟨notMerged, notHigh, _, start, advance⟩
  · have other (t) : b.arc t ≠ 0 := fun same => b.river_ne_arc t (merged.trans same.symm)
    rcases comparison with ⟨start, _⟩ | ⟨descending, low⟩ | ⟨_, finish⟩
    · rcases original_step_shape (b.arcStep 0) with ⟨row,_⟩ | ⟨_,first,_⟩ | ⟨_,apart,_,first,_⟩
      · exact other _ row
      · exact high_ne_zero (start.symm.trans first)
      · exact apart (first.symm.trans start)
    · have nondecreasing (t : Fin (d+2)) : (b.vertex 0).val ≤ (b.vertex t).val := by
        induction t using Fin.induction with
        | zero => exact le_rfl
        | succ t ih => exact ih.trans (unmerged_step_increases (other t) (b.arcStep t)).le
      have rank := nondecreasing final
      rcases descending with high | next <;> rcases low with zero | one
      · rw [high, zero] at rank; change extra+3 ≤ 0 at rank; omega
      · rw [high, one] at rank; change extra+3 ≤ 1 at rank; omega
      · rw [next, zero] at rank; change extra+4 ≤ 0 at rank; omega
      · rw [next, one] at rank; change extra+4 ≤ 1 at rank; omega
    · rcases original_step_shape endStep with ⟨row,_⟩ | ⟨_,_,arrives⟩ | ⟨notZero,_,_,leaves,move⟩
      · exact other _ row
      · have equal := congrArg Fin.val (finish.symm.trans arrives)
        change 1 = extra+6 at equal
        omega
      · apply notZero
        apply Fin.ext
        rw [finish, leaves] at move
        change 1 = (b.arc endArc).val+1 at move
        change (b.arc endArc).val = 0
        omega
  · have first : b.arc 0 = 0 ∧ b.vertex (Fin.succ 0) = 1 := by
      rcases original_step_shape (b.arcStep 0) with ⟨row, comparison⟩ | ⟨same,_,_⟩ |
        ⟨notZero,_,_,leaves,_⟩
      · rcases comparison with ⟨first,_⟩ | ⟨first,_⟩ | ⟨_,second⟩
        · exact (high_ne_zero (first.symm.trans start)).elim
        · exact (first.elim (fun eq => high_ne_zero (eq.symm.trans start))
            (fun eq => next_ne_zero (eq.symm.trans start))).elim
        · exact ⟨row,second⟩
      · exact (b.river_ne_arc 0 (river.trans same.symm)).elim
      · exact (notZero (leaves.symm.trans start)).elim
    have bounded (t : Fin (d+1)) : (b.vertex t.succ).val ≤ extra+3 := by
      induction t using Fin.induction with
      | zero => rw [first.2]; change 1 ≤ extra+3; omega
      | succ t ih =>
        have later : b.arc t.succ ≠ 0 := fun same =>
          Fin.succ_ne_zero t (b.distinctArcs (same.trans first.1.symm))
        have other : b.arc t.succ ≠ terminal extra := fun same => b.river_ne_arc _ (river.trans same.symm)
        obtain ⟨notHigh,leaves,move⟩ := dart_step later other (b.arcStep t.succ)
        have oldBound : (b.vertex t.succ.castSucc).val ≤ extra+3 := by
          simpa only [Fin.succ_castSucc] using ih
        have below : (b.vertex t.succ.castSucc).val ≠ extra+3 := fun equal =>
          notHigh (leaves.symm.trans (Fin.ext equal))
        omega
    have upper := bounded (Fin.last d)
    rw [Fin.succ_last] at upper
    change (b.vertex final).val ≤ extra+3 at upper
    rw [finish] at upper
    change extra+6 ≤ extra+3 at upper
    omega
  · by_cases atTerminal : b.vertex final = terminal extra
    · have startRank : (b.vertex 0).val = extra+5 := by
        rw [atTerminal] at advance
        change extra+6 = (b.vertex 0).val+1 at advance
        omega
      change (b.vertex ((0 : Fin (d+1)).castSucc)).val = extra+5 at startRank
      rcases original_step_shape (b.arcStep 0) with ⟨_,hi | reverse | low⟩ | ⟨_,first,_⟩ | ⟨_,_,_,first,_⟩
      · rw [hi.1] at startRank; change extra+3 = extra+5 at startRank; omega
      · rcases reverse.1 with high | next
        · rw [high] at startRank; change extra+3 = extra+5 at startRank; omega
        · rw [next] at startRank; change extra+4 = extra+5 at startRank; omega
      · rw [low.1] at startRank; change 0 = extra+5 at startRank; omega
      · rw [first] at startRank; change 0 = extra+5 at startRank; omega
      · exact b.river_ne_arc _ (start.symm.trans first)
    · rcases original_step_shape endStep with ⟨_,hi | reverse | low⟩ | ⟨_,_,last⟩ | ⟨_,_,_,first,move⟩
      · apply notHigh
        apply Fin.ext
        rw [hi.2, start] at advance
        change extra+4 = (b.river).val+1 at advance
        change (b.river).val = extra+3
        omega
      · rcases reverse.2 with zero | one
        · rw [zero] at advance; change 0 = (b.vertex 0).val+1 at advance; omega
        · apply notMerged
          apply Fin.ext
          rw [one, start] at advance
          change 1 = (b.river).val+1 at advance
          change (b.river).val = 0
          omega
      · apply notMerged
        apply Fin.ext
        rw [low.2, start] at advance
        change 1 = (b.river).val+1 at advance
        change (b.river).val = 0
        omega
      · exact atTerminal last
      · apply b.river_ne_arc endArc
        apply Fin.ext
        rw [start] at advance
        rw [first] at move
        exact Nat.add_right_cancel (advance.symm.trans move)

private theorem low_piece (extra : ℕ) : fullReturnSharpPieces extra 0 = [0,1] := by
  rw [fullReturnSharpPieces, ite_eq_right terminal_ne_zero.symm, zero_add]

private theorem high_piece (extra : ℕ) :
    fullReturnSharpPieces extra (highCorner extra) = [highCorner extra, nextCorner extra] := by
  have next : highCorner extra + 1 = nextCorner extra := Fin.ext (successor_val terminal_ne_high.symm)
  rw [fullReturnSharpPieces, ite_eq_right terminal_ne_high.symm, next]

private theorem apart_with_same_parent {extra : ℕ} {i j : SharpVertex extra} (apart : i ≠ j)
    (same : fullReturnSharpParent extra i = fullReturnSharpParent extra j) :
    (i = highCorner extra ∧ j = 0) ∨ (i = 0 ∧ j = highCorner extra) := by
  by_cases highI : i = highCorner extra
  · subst i
    exact Or.inl ⟨rfl, by simpa [fullReturnSharpParent, apart.symm] using same.symm⟩
  by_cases highJ : j = highCorner extra
  · subst j
    exact Or.inr ⟨by simpa [fullReturnSharpParent, highI] using same, rfl⟩
  exact (apart (by simpa [fullReturnSharpParent, highI, highJ] using same)).elim

theorem fullReturnSharpRows_simple (extra : ℕ) (i : SharpVertex extra) :
    (fullReturnSharpRows extra i).Nodup := by
  by_cases atZero : i = 0
  · subst i
    simp [fullReturnSharpRows, Ne.symm]
  by_cases atHigh : i = highCorner extra
  · simp [fullReturnSharpRows, atHigh]
  rw [fullReturnSharpRows, ite_eq_right atZero, ite_eq_right atHigh, fullReturnSharpPieces]
  by_cases last : i = terminal extra
  · simp [last, terminal_ne_zero.symm]
  · simp [last, successor_ne last]

/-- Splitting just the merged row gives order-preserving sublists. -/
theorem fullReturnSharpPieces_sublist (extra : ℕ) (i : SharpVertex extra) :
    (fullReturnSharpPieces extra i).Sublist (fullReturnSharpRows extra (fullReturnSharpParent extra i)) := by
  by_cases atHigh : i = highCorner extra
  · subst i
    rw [high_piece, fullReturnSharpParent, ite_eq_left rfl, fullReturnSharpRows, ite_eq_left rfl]
    exact .cons_cons _ (.cons_cons _ (.cons _ (.cons _ .slnil)))
  rw [fullReturnSharpParent, ite_eq_right atHigh]
  by_cases atZero : i = 0
  · subst i
    rw [low_piece, fullReturnSharpRows, ite_eq_left rfl]
    exact .cons _ (.cons _ (.refl _))
  rw [fullReturnSharpRows, ite_eq_right atZero, ite_eq_right atHigh]

theorem fullReturnSharpPieces_disjoint {extra : ℕ} {i j x : SharpVertex extra} (apart : i ≠ j)
    (same : fullReturnSharpParent extra i = fullReturnSharpParent extra j)
    (left : x ∈ fullReturnSharpPieces extra i) (right : x ∈ fullReturnSharpPieces extra j) : False := by
  have noOverlap : x ∈ fullReturnSharpPieces extra (highCorner extra) →
      x ∈ fullReturnSharpPieces extra 0 → False := by
    rw [high_piece,low_piece]
    intro high low
    have highChoices : x = highCorner extra ∨ x = nextCorner extra := by simpa using high
    rcases highChoices with rfl | rfl <;> simp at low
  rcases apart_with_same_parent apart same with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · exact noOverlap left right
  · exact noOverlap right left

theorem fullReturnSharpPieces_cover {extra : ℕ} {i x : SharpVertex extra}
    (onRow : x ∈ fullReturnSharpRows extra i) :
    ∃ j, fullReturnSharpParent extra j = i ∧ x ∈ fullReturnSharpPieces extra j := by
  by_cases atZero : i = 0
  · subst i
    have on : x = highCorner extra ∨ x = nextCorner extra ∨ x = 0 ∨ x = 1 := by
      simpa [fullReturnSharpRows] using onRow
    rcases on with high | next | zero | one
    · exact ⟨highCorner extra, by simp [fullReturnSharpParent], by simp [high_piece, high]⟩
    · exact ⟨highCorner extra, by simp [fullReturnSharpParent], by simp [high_piece, next]⟩
    · exact ⟨0, by simp [fullReturnSharpParent, high_ne_zero.symm], by simp [low_piece, zero]⟩
    · exact ⟨0, by simp [fullReturnSharpParent, high_ne_zero.symm], by simp [low_piece, one]⟩
  by_cases atHigh : i = highCorner extra
  · simp [fullReturnSharpRows, atHigh] at onRow
  exact ⟨i, by simp [fullReturnSharpParent, atHigh], by simpa [fullReturnSharpRows, atZero, atHigh] using onRow⟩

/-- Every step of the terminal detour now uses a distinct row. -/
theorem fullReturnSharpPieces_creates_bridge (extra : ℕ) :
    Nonempty (Bridge (BeforeIn (fullReturnSharpPieces extra)) (extra+5)) := by
  have follows (i : Fin (extra+5+1)) :
      BeforeIn (fullReturnSharpPieces extra) i.castSucc i.castSucc i.succ := by
    have notLast : i.castSucc ≠ terminal extra := different_of_values (by
      rw [Fin.val_castSucc]
      change i.val ≠ extra+6
      have := i.isLt
      omega)
    have next : i.castSucc + 1 = i.succ := Fin.ext (successor_val notLast)
    exact (pair_step (ite_eq_right notLast) (successor_ne notLast)).mpr ⟨rfl, next.symm⟩
  have river : BeforeIn (fullReturnSharpPieces extra) (terminal extra) 0 (terminal extra) :=
    (pair_step (ite_eq_left rfl) terminal_ne_zero.symm).mpr ⟨rfl,rfl⟩
  refine ⟨⟨id, Fin.castSucc, terminal extra, Function.injective_id, Fin.castSucc_injective _, ?_, river, follows⟩⟩
  intro i equal
  have values := congrArg Fin.val equal
  change extra+6 = i.val at values
  have := i.isLt
  omega

private abbrev sharpPieceGraph (extra : ℕ) : Arcs (SharpVertex extra) :=
  listPiecePrecedenceGraph (fullReturnSharpPieces extra)

private theorem sharp_edge_increases {extra : ℕ} {x y : SharpVertex extra}
    (edge : Edge (sharpPieceGraph extra) x y) : x.val < y.val := by
  obtain ⟨_,step⟩ := listPiecePrecedenceGraph_edge.mp edge
  rcases piece_step_shape step with ⟨_,first,last⟩ | ⟨_,_,advance⟩
  · rw [first,last]
    change 0 < extra+6
    omega
  · omega

private theorem sharp_reach_nondecreasing {extra : ℕ} {x y : SharpVertex extra}
    {d : ℕ} (walk : x ∈ reachIn (sharpPieceGraph extra) y d) : x.val ≤ y.val := by
  have connected := reachIn_sound walk
  clear walk
  induction connected with
  | refl => exact le_rfl
  | tail _ edge previous => exact previous.trans (sharp_edge_increases edge).le

private theorem sharp_reach_length {extra : ℕ} {x y : SharpVertex extra}
    (target : y.val ≤ extra+4) {d : ℕ} (walk : x ∈ reachIn (sharpPieceGraph extra) y d) :
    y.val ≤ x.val+d := by
  induction d generalizing x with
  | zero =>
    have same : x = y := by simpa only [reachIn,mem_singleton] using walk
    simp [same]
  | succ d ih =>
    rcases reachIn_succ.mp walk with earlier | ⟨z,edge,rest⟩
    · exact (ih earlier).trans (by omega)
    · have zRank := sharp_reach_nondecreasing rest
      obtain ⟨_,step⟩ := listPiecePrecedenceGraph_edge.mp edge
      rcases piece_step_shape step with ⟨_,_,terminalTarget⟩ | ⟨_,_,successor⟩
      · rw [terminalTarget] at zRank
        change extra+6 ≤ y.val at zRank
        omega
      · have remaining := ih rest
        omega

/-- Every backward crossing in the actual pieces takes at least
one more step than this radius allows. -/
theorem fullReturnSharpPieces_short_test (extra : ℕ) :
    NoShortBackwardReturnAcrossPieces (sharpPieceGraph extra) id (fullReturnSharpRows extra)
      (fullReturnSharpPieces extra) (fullReturnSharpParent extra) (extra+1) := by
  intro i j x y apart same first last compare returnWalk
  change y ∈ reachIn (sharpPieceGraph extra) x (extra+1) at returnWalk
  have highRank {v : SharpVertex extra} (on : v ∈ fullReturnSharpPieces extra (highCorner extra)) :
      extra+3 ≤ v.val ∧ v.val ≤ extra+4 := by
    have choices : v = highCorner extra ∨ v = nextCorner extra := by simpa [high_piece] using on
    rcases choices with rfl | rfl
    · change extra+3 ≤ extra+3 ∧ extra+3 ≤ extra+4; omega
    · change extra+3 ≤ extra+4 ∧ extra+4 ≤ extra+4; omega
  have lowRank {v : SharpVertex extra} (on : v ∈ fullReturnSharpPieces extra 0) : v.val ≤ 1 := by
    have choices : v = 0 ∨ v = 1 := by simpa [low_piece] using on
    rcases choices with rfl | rfl
    · change 0 ≤ 1; omega
    · exact le_rfl
  rcases apart_with_same_parent apart same with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · have high := highRank first
    have low := lowRank last
    have length := sharp_reach_length high.2 returnWalk
    omega
  · have step : BeforeIn (fullReturnSharpRows extra) 0 x y := by
      simpa [fullReturnSharpParent, high_ne_zero.symm] using compare
    have low := lowRank first
    have high := (highRank last).1
    rcases long_step_shape step with ⟨upper,_⟩ | ⟨upper,_⟩ | ⟨_,lower⟩
    · rw [upper] at low; change extra+3 ≤ 1 at low; omega
    · rcases upper with hi | next
      · rw [hi] at low; change extra+3 ≤ 1 at low; omega
      · rw [next] at low; change extra+4 ≤ 1 at low; omega
    · rw [lower] at high; change extra+3 ≤ 1 at high; omega

/-- The path from one to the high corner attains the first crossing
length on the actual pieces. -/
theorem fullReturnSharpPieces_exact_return (extra : ℕ) :
    (1 : SharpVertex extra) ∈ reachIn (sharpPieceGraph extra) (highCorner extra) (extra+2) := by
  let chain (j : Fin (extra+3)) : SharpVertex extra := ⟨1+j.val, by have := j.isLt; omega⟩
  have edges (i : Fin (extra+2)) : Edge (sharpPieceGraph extra) (chain i.castSucc) (chain i.succ) := by
    let start := chain i.castSucc
    have notLast : start ≠ terminal extra := different_of_values (by
      change 1+i.val ≠ extra+6
      have := i.isLt
      omega)
    have next : start+1 = chain i.succ := Fin.ext (by
      rw [successor_val notLast]
      change 1+i.val+1 = 1+(i.val+1)
      omega)
    exact listPiecePrecedenceGraph_edge.mpr ⟨start,
      (pair_step (ite_eq_right notLast) (successor_ne notLast)).mpr ⟨rfl, next.symm⟩⟩
  have first : chain 0 = 1 := Fin.ext rfl
  have last : chain (Fin.last (extra+2)) = highCorner extra := Fin.ext (by
    change 1+(extra+2) = extra+3
    omega)
  simpa only [first,last] using reachIn_of_fin_steps chain edges

/-- The exact crossing fails the return test at the sufficient radius. -/
theorem fullReturnSharpPieces_exact_test_fails (extra : ℕ) :
    ¬ NoShortBackwardReturnAcrossPieces (sharpPieceGraph extra) id (fullReturnSharpRows extra)
      (fullReturnSharpPieces extra) (fullReturnSharpParent extra) (extra+2) := by
  intro safe
  have same : fullReturnSharpParent extra (highCorner extra) = fullReturnSharpParent extra 0 := by
    simp [fullReturnSharpParent, high_ne_zero.symm]
  have first : highCorner extra ∈ fullReturnSharpPieces extra (highCorner extra) := by simp [high_piece]
  have last : (1 : SharpVertex extra) ∈ fullReturnSharpPieces extra 0 := by simp [low_piece]
  have compare : BeforeIn (fullReturnSharpRows extra) (fullReturnSharpParent extra (highCorner extra))
      (highCorner extra) 1 := by
    simp [BeforeIn, fullReturnSharpRows, fullReturnSharpParent, Ne.symm]
  exact safe high_ne_zero same first last compare (fullReturnSharpPieces_exact_return extra)

/-- At each full cutoff from seven, a one-step smaller graph radius
can accept a covering disjoint split that creates a forbidden bridge. -/
theorem full_return_radius_sharp (cutoff : ℕ) (large : 7 ≤ cutoff) :
    ∃ (rows pieces : Fin cutoff → List (Fin cutoff)) (parent : Fin cutoff → Fin cutoff),
      (∀ i, (rows i).Nodup) ∧ (∀ k, BridgeFree (BeforeIn rows) k) ∧
      (∀ i, (pieces i).Sublist (rows (parent i))) ∧
      (∀ ⦃i j x⦄, i ≠ j → parent i = parent j → x ∈ pieces i → x ∈ pieces j → False) ∧
      (∀ ⦃i x⦄, x ∈ rows i → ∃ j, parent j = i ∧ x ∈ pieces j) ∧
      NoShortBackwardReturnAcrossPieces (listPiecePrecedenceGraph pieces) id rows pieces parent (cutoff-6) ∧
      ¬ NoShortBackwardReturnAcrossPieces (listPiecePrecedenceGraph pieces) id rows pieces parent (cutoff-5) ∧
      ¬ BridgeFree (BeforeIn pieces) cutoff := by
  have size : ∃ extra, cutoff = extra+7 := ⟨cutoff-7, by omega⟩
  obtain ⟨extra,rfl⟩ := size
  refine ⟨fullReturnSharpRows extra, fullReturnSharpPieces extra, fullReturnSharpParent extra,
    fullReturnSharpRows_simple extra, fullReturnSharpRows_fullFree extra,
    fullReturnSharpPieces_sublist extra, (fun {_ _ _} => fullReturnSharpPieces_disjoint),
    (fun {_ _} => fullReturnSharpPieces_cover), ?_, ?_, ?_⟩
  · rw [show extra+7-6 = extra+1 by omega]
    exact fullReturnSharpPieces_short_test extra
  · rw [show extra+7-5 = extra+2 by omega]
    exact fullReturnSharpPieces_exact_test_fails extra
  · intro absent
    obtain ⟨b⟩ := fullReturnSharpPieces_creates_bridge extra
    exact (absent (show extra+5+2 ≤ extra+7 by omega)).false b

end OnlineReachabilityPreservers.SourceAudit
