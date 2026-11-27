import OnlineReachabilityPreservers.WengerThreeRows
import OnlineReachabilityPreservers.LocalFrozenCleaning
import OnlineReachabilityPreservers.DistinctPathBudgets

/-! A frozen-average full-three witness at equal finite-field cubic budgets. -/

namespace OnlineReachabilityPreservers

open Finset
local notation "Before" => SourceAudit.BeforeIn

/-- At equal cubic budgets of field scale at least eleven, the total
half-three mass is at most four times the mass of the regular line family. -/
theorem half_three_mass_le_four_on_cube_budgets {q k : ℕ} (large : 11 ≤ q)
    (paths : Fin (q^3) → List (Fin (q^3))) (simple : ∀ i, (paths i).Nodup)
    (half : HalfBridgeFree (Before paths) k) (three : 3 ≤ k) : (∑ i, (paths i).length) ≤ 4*q^4 := by
  have qPos : 0 < q := by omega
  have bound := half_three_shifted_mass_cube_le (by positivity) (by positivity) paths simple half three
  by_contra! excess
  let D := 4*q^3*(q-1)
  have reference : D+2*(q^3+q^3) = 4*q^4 := calc
    _ = 4*q^3*((q-1)+1) := by dsimp only [D]; ring
    _ = _ := by rw [Nat.sub_add_cancel (by omega : 1 ≤ q)]; ring
  have shift : D < (∑ i, (paths i).length)-2*(q^3+q^3) := by omega
  have qComparison : 6*q^3 ≤ 8*(q-1)^3 := by
    have scale : 10*q ≤ 11*(q-1) := by omega
    apply Nat.le_of_mul_le_mul_left (c := 1331) _ (by decide)
    calc
      _ = 7986*q^3 := by ring
      _ ≤ 8000*q^3 := Nat.mul_le_mul_right _ (by decide)
      _ = 8*(10*q)^3 := by ring
      _ ≤ 8*(11*(q-1))^3 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left scale 3)
      _ = _ := by ring
  have gap : 48*(q^3*q^3)^2 ≤ D^3 := calc
    _ = (8*q^9)*(6*q^3) := by ring
    _ ≤ (8*q^9)*(8*(q-1)^3) := Nat.mul_le_mul_left _ qComparison
    _ = _ := by dsimp only [D]; ring
  have contrad := gap.trans_lt (pow_lt_pow_left₀ shift (Nat.zero_le _) (by decide : 3 ≠ 0))
  exact (not_lt_of_ge bound) contrad

/-- At the literal half maximum for equal cubic budgets over a finite
field of size at least eleven, the regular line family gives the four
starting-average caps and a mass between one quarter and all of the
maximum. The full witness uses the exact original budgets and cutoff three. -/
theorem literal_frozen_full_three_at_field_cube_maximum (F : Type*) [Field F] [Fintype F]
    (large : 11 ≤ Fintype.card F)
    (paths : Fin ((Fintype.card F)^3) → List (Fin ((Fintype.card F)^3)))
    (simple : ∀ i, (paths i).Nodup) (half : HalfBridgeFree (Before paths) 3)
    (maximal : ∀ rhs : Fin ((Fintype.card F)^3) → List (Fin ((Fintype.card F)^3)),
      Function.Injective rhs → (∀ i, rhs i ≠ [] ∧ (rhs i).Nodup) → HalfBridgeFree (Before rhs) 3 →
      (∑ i, (rhs i).length) ≤ ∑ i, (paths i).length) :
    let q := Fintype.card F
    let M := ∑ i, (paths i).length
    ∃ rows : Fin (q^3) → List (Fin (q^3)), Function.Injective rows ∧
      (∀ i, rows i ≠ [] ∧ (rows i).Nodup) ∧ BridgeFree (Before rows) 3 ∧
      (∑ i, (rows i).length) = q^4 ∧ (∑ i, (rows i).length) ≤ M ∧ M ≤ 4*(∑ i, (rows i).length) ∧
      frozenListCaps (q^3) (q^3) M rows := by
  let q := Fintype.card F
  let M := ∑ i, (paths i).length
  have qPos : 0 < q := Fintype.card_pos
  obtain ⟨rows,injective,lengths,free,mass,degree,_⟩ := wenger_full_three_rows F
  have present (i : Fin (q^3)) : rows i ≠ [] ∧ (rows i).Nodup := by
    refine ⟨fun no => ?_,(lengths i).1⟩
    have len := (lengths i).2
    rw [no,List.length_nil] at len
    exact (Nat.ne_of_gt qPos) len.symm
  have limit : (∑ i, (rows i).length) ≤ M := maximal rows injective present free.halfFree
  have lower : q^4 ≤ M := mass.symm.trans_le limit
  have upper : M ≤ 4*q^4 := half_three_mass_le_four_on_cube_budgets large paths simple half le_rfl
  have retention : M ≤ 4*(∑ i, (rows i).length) := by rw [mass]; exact upper
  have lowerR : (q:ℝ)^4 ≤ M := by exact_mod_cast lower
  have upperR : (M:ℝ) ≤ 4*(q:ℝ)^4 := by exact_mod_cast upper
  have posR : 0 < (q:ℝ) := Nat.cast_pos.mpr qPos
  have degreeLower : (M:ℝ)/(4*(q:ℝ)^3) ≤ q := by
    apply (div_le_iff₀ (by positivity)).mpr
    convert upperR using 1
    ring
  have degreeUpper : (q:ℝ) ≤ 4*(M:ℝ)/(q:ℝ)^3 := by
    apply (le_div_iff₀ (by positivity)).mpr
    calc
      _ = (q:ℝ)^4 := by ring
      _ ≤ _ := by linarith only [lowerR,show (0:ℝ) ≤ M by positivity]
  have caps : frozenListCaps (q^3) (q^3) M rows := by
    simp only [frozenListCaps,Nat.cast_pow,degree,fun i => (lengths i).2]
    exact ⟨fun _ => ⟨degreeLower,degreeUpper⟩,fun _ => ⟨degreeLower,degreeUpper⟩⟩
  exact ⟨rows,injective,present,free,mass,limit,retention,caps⟩

/-- The literal exact-count half maximum exists at these budgets, and
the same-budget full witness realizes the frozen-cap conclusion. -/
theorem localOrderDistinctExtremal_frozen_full_three_at_field_cube (F : Type*) [Field F] [Fintype F]
    (large : 11 ≤ Fintype.card F) :
    let q := Fintype.card F
    ∃ paths : Fin (q^3) → List (Fin (q^3)), Function.Injective paths ∧
      (∀ i, paths i ≠ [] ∧ (paths i).Nodup) ∧ HalfBridgeFree (Before paths) 3 ∧
      (∀ other : Fin (q^3) → List (Fin (q^3)), Function.Injective other →
        (∀ i, other i ≠ [] ∧ (other i).Nodup) → HalfBridgeFree (Before other) 3 →
        (∑ i, (other i).length) ≤ ∑ i, (paths i).length) ∧
      let M := ∑ i, (paths i).length
      ∃ rows : Fin (q^3) → List (Fin (q^3)), Function.Injective rows ∧
        (∀ i, rows i ≠ [] ∧ (rows i).Nodup) ∧ BridgeFree (Before rows) 3 ∧
        (∑ i, (rows i).length) = q^4 ∧ (∑ i, (rows i).length) ≤ M ∧ M ≤ 4*(∑ i, (rows i).length) ∧
        frozenListCaps (q^3) (q^3) M rows := by
  let q := Fintype.card F
  have qPos : 0 < q := Fintype.card_pos
  obtain ⟨rows,injective,lengths,free,_,_,_⟩ := wenger_full_three_rows F
  have present (i : Fin (q^3)) : rows i ≠ [] ∧ (rows i).Nodup := by
    refine ⟨fun no => ?_,(lengths i).1⟩
    have len := (lengths i).2
    rw [no,List.length_nil] at len
    exact (Nat.ne_of_gt qPos) len.symm
  obtain ⟨paths,distinct,valid,half,maximal,_,_⟩ := localOrderDistinctExtremal_isDense (k := 3) true
    (show 0 < q^3 by positivity) ⟨rows,injective,present,free.halfFree⟩
  exact ⟨paths,distinct,valid,half,maximal,literal_frozen_full_three_at_field_cube_maximum F large
    paths (fun i => (valid i).2) half maximal⟩

end OnlineReachabilityPreservers
