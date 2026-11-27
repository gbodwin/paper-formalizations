import Mathlib.Algebra.Group.Fin.Basic
import OnlineReachabilityPreservers.LocalRegularization
import OnlineReachabilityPreservers.OrderedLatticeAsymptoticGap

/-! The separation with the positive slopes and rectangle counts of Bridge Girth. -/

namespace OnlineReachabilityPreservers

open Finset
local notation "Before" => SourceAudit.BeforeIn

variable {steps rows slopes starts : ℕ}

/-- Translate the height by the layer index, with modular arithmetic
on the ambient rectangle. Actual line vertices do not wrap when there
is room for the positive slopes. -/
def latticeHeightShift (steps rows : ℕ) [NeZero rows] : LayerGrid steps rows ≃ LayerGrid steps rows where
  toFun v := (v.1, v.2 + Fin.ofNat rows v.1.val)
  invFun v := (v.1, v.2 - Fin.ofNat rows v.1.val)
  left_inv v := Prod.ext rfl (add_sub_cancel_right v.2 _)
  right_inv v := Prod.ext rfl (sub_add_cancel v.2 _)

/-- Use slopes one through `slopes` by applying the same height shift
to every line. -/
def positiveSlopeLatticeRows [NeZero rows] (fit : LatticeFits steps rows slopes starts)
    (line : LatticeLine slopes starts) : List (LayerGrid steps rows) :=
  (orderedLatticeRows fit line).map (latticeHeightShift steps rows)

/-- On a line vertex the shift adds the layer without wrapping, so the
result lies on the line of slope one more than its zero-based label. -/
theorem positiveSlopeLatticeRows_height [NeZero rows] {fit : LatticeFits steps rows slopes starts}
    (room : starts+steps*slopes ≤ rows) {line : LatticeLine slopes starts} {v : LayerGrid steps rows}
    (member : v ∈ positiveSlopeLatticeRows fit line) :
    v.2.val = (ofLex line).2.val + v.1.val * ((ofLex line).1.val+1) := by
  obtain ⟨old,on,rfl⟩ := List.mem_map.mp member
  obtain ⟨layer,rfl⟩ := List.mem_ofFn.mp on
  have layerBound : layer.val ≤ steps := Nat.le_of_lt_succ layer.isLt
  have mulBound := Nat.mul_le_mul layerBound (Nat.succ_le_of_lt (ofLex line).1.isLt)
  have heightBound := (Nat.add_lt_add_of_lt_of_le (ofLex line).2.isLt mulBound).trans_le room
  change ((latticeVertex fit line layer).2 + Fin.ofNat rows layer.val).val = _
  rw [Fin.add_ofNat]
  change ((ofLex line).2.val + layer.val*(ofLex line).1.val + layer.val) % rows =
    (ofLex line).2.val + layer.val*((ofLex line).1.val+1)
  rw [show (ofLex line).2.val + layer.val*(ofLex line).1.val + layer.val =
      (ofLex line).2.val + layer.val*((ofLex line).1.val+1) by ring]
  exact Nat.mod_eq_of_lt heightBound

/-- The height shift preserves the all-arcs-earlier condition because
pulling back a bridge keeps its path labels and every local comparison. -/
theorem positiveSlopeLatticeRows_no_bridge_with_all_arcs_earlier [NeZero rows]
    (fit : LatticeFits steps rows slopes starts) {d : ℕ}
    (b : Bridge (Before (positiveSlopeLatticeRows fit)) d) : ¬ ∀ i, b.arc i < b.river := by
  let shift := (latticeHeightShift steps rows).symm
  have recover (i : LatticeLine slopes starts) : ((positiveSlopeLatticeRows fit i).map shift) =
      orderedLatticeRows fit i := by
    simp [positiveSlopeLatticeRows,shift,List.map_map,Function.comp_def]
  have step {i x y} (forward : Before (positiveSlopeLatticeRows fit) i x y) :
      Before (orderedLatticeRows fit) i (shift x) (shift y) := by
    have original := listBefore_map shift ((recover i).symm ▸ orderedLatticeRows_simple fit i) forward
    unfold SourceAudit.BeforeIn at original ⊢
    simpa only [recover] using original
  let old := b.mapVertices shift shift.injective (fun _ _ _ forward => step forward)
  exact orderedLatticeRows_no_bridge_with_all_arcs_earlier fit old

/-- Use `ℓ` layers, `2ℓ²` heights, the first `ℓ²` starts and slopes
one through `ℓ`. These are Theorem 29's rectangle counts at `2ℓ³`
vertices. The polynomial gap holds at these same budgets. -/
theorem theorem29_positive_lattice_gap_over_half_four :
    ∃ A ≥ (1:ℝ), ∀ steps : ℕ,
      let ℓ := steps+1
      ∃ family : LatticeLine ℓ (ℓ^2) → List (LayerGrid steps (2*ℓ^2)),
        Function.Injective family ∧ (∀ line, (family line).Nodup ∧ (family line).length = ℓ) ∧
        (∀ line v, v ∈ family line →
          v.2.val = (ofLex line).2.val + v.1.val*((ofLex line).1.val+1)) ∧
        (∀ d (b : Bridge (Before family) d), ¬ ∀ i, b.arc i < b.river) ∧
        ∀ {n p : ℕ}, n ≤ 2*ℓ^3 → p ≤ ℓ^3 → ∀ paths : Fin p → List (Fin n),
          (∀ i, (paths i).Nodup) → HalfBridgeFree (Before paths) 4 →
          (ℓ:ℝ) ^ (1/10:ℝ) * (∑ i, ((paths i).length : ℝ)) ≤ A * ∑ line, ((family line).length : ℝ) := by
  obtain ⟨A,Aone,gap⟩ := ordered_lattice_polynomial_gap_over_half_four
  refine ⟨2*A,by linarith,?_⟩
  intro steps
  let ℓ := steps+1
  have ℓpos : 0 < ℓ := Nat.succ_pos steps
  have ℓone : 1 ≤ ℓ := ℓpos
  have floor : steps*ℓ ≤ ℓ*ℓ := Nat.mul_le_mul_right ℓ (Nat.le_succ _)
  have room : ℓ^2+steps*ℓ ≤ 2*ℓ^2 := by nlinarith only [floor]
  have fit : LatticeFits steps (2*ℓ^2) ℓ (ℓ^2) :=
    (Nat.add_le_add_left (Nat.mul_le_mul_left steps (Nat.sub_le ℓ 1)) _).trans room
  have heights : 0 < 2*ℓ^2 := by positivity
  let _ : NeZero (2*ℓ^2) := ⟨heights.ne'⟩
  let family := positiveSlopeLatticeRows fit
  have lengths (line : LatticeLine ℓ (ℓ^2)) : (family line).length = ℓ := by
    simp [family,positiveSlopeLatticeRows,orderedLatticeRows,ℓ]
  refine ⟨family,?_,?_,?_,?_,?_⟩
  · intro a b equal
    by_cases positive : 0 < steps
    · apply orderedLatticeRows_injective_of_steps fit positive
      exact List.map_injective_iff.mpr (latticeHeightShift steps (2*ℓ^2)).injective equal
    · obtain rfl : steps = 0 := by omega
      apply ofLex.injective
      apply Prod.ext <;> apply Fin.ext
      · have left : (ofLex a).1.val < 1 := (ofLex a).1.isLt
        have right : (ofLex b).1.val < 1 := (ofLex b).1.isLt
        omega
      · have left : (ofLex a).2.val < 1 := (ofLex a).2.isLt
        have right : (ofLex b).2.val < 1 := (ofLex b).2.isLt
        omega
  · intro line
    exact ⟨(orderedLatticeRows_simple fit line).map (latticeHeightShift steps (2*ℓ^2)).injective,lengths line⟩
  · intro line v member
    exact positiveSlopeLatticeRows_height room member
  · intro d b
    exact positiveSlopeLatticeRows_no_bridge_with_all_arcs_earlier fit b
  · intro n p vertices pathsBound paths simple free
    obtain ⟨oldFit,_,oldLength,_,compare⟩ := gap ℓ ℓpos
    have vertexRoom : 2*ℓ^3 ≤ (ℓ+1)*(2*ℓ^2) := by
      calc
        _ = ℓ*(2*ℓ^2) := by ring
        _ ≤ _ := Nat.mul_le_mul_right _ (Nat.le_succ _)
    have estimate := compare (vertices.trans vertexRoom) pathsBound paths simple free
    have mass : (∑ line, ((orderedLatticeRows oldFit line).length : ℝ)) ≤ 2 * ∑ line, ((family line).length : ℝ) := by
      rw [Finset.mul_sum]
      apply sum_le_sum
      intro line _
      rw [(oldLength line).2,lengths line]
      exact_mod_cast (show ℓ+1 ≤ 2*ℓ by omega)
    exact estimate.trans ((mul_le_mul_of_nonneg_left mass (by linarith)).trans_eq (by ring))

end OnlineReachabilityPreservers
