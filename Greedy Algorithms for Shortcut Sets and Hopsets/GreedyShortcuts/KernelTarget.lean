import GreedyShortcuts.KernelBalance
import Mathlib.Data.Nat.Sqrt

/-! Integer target selection for an explicit small-kernel certificate.
Every division, positive-target hypothesis and size bound is exposed. -/
namespace GreedyShortcuts.KernelTarget

open DirectedPaths

def parameter (Z B : ℕ) : ℕ := max 8 (Nat.sqrt (7*Z/B)+1)

theorem parameter_ge (Z B : ℕ) : 8 ≤ parameter Z B := Nat.le_max_left _ _

theorem target_square (Z B : ℕ) (hB : 0 < B) : 7*Z ≤ B*(parameter Z B)^2 := by
  have hs := Nat.succ_le_succ_sqrt' (7*Z/B)
  have hp : Nat.sqrt (7*Z/B)+1 ≤ parameter Z B := Nat.le_max_right _ _
  have hsq := Nat.pow_le_pow_left hp 2
  have hdiv : 7*Z < B*(7*Z/B+1) := by
    have hrem := Nat.mod_lt (7*Z) hB
    have he := Nat.mod_add_div (7*Z) B
    nlinarith
  have hm := Nat.mul_le_mul_left B (hs.trans hsq)
  omega

variable {V W : Type*} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
variable {G : V → V → Prop} {R L : ℕ} (A : KernelLift.Kernel G W R L)

/-- The actual output meets the requested target for this explicitly rounded
inner parameter, provided the supplied kernel has the stated scale. -/
theorem output_hop (Z B : ℕ) (hB : 0 < B) (hL : 1 ≤ L) (hR : R ≤ L)
    (hscale : L*(parameter Z B)^3 ≤ Z) {s t : V} (hr : Reachable G s t) :
    hopDist (augment G (A.output (parameter Z B) (by have := parameter_ge Z B;omega))) s t ≤ B := by
  have hb := parameter_ge Z B
  have hp := KernelBalance.output_hop_scaled A (parameter Z B) (by omega) hL hR Z hscale hr
  have hs := target_square Z B hB
  exact Nat.le_of_mul_le_mul_right (hp.trans (by simpa [Nat.mul_comm] using hs)) (by positivity)

/-- A fully finite square-root/cubic presentation of the selected edge count.
Kernel existence and the certificate scale remain visible hypotheses. -/
theorem output_card (Z B : ℕ) (hW : Fintype.card W ≤ (parameter Z B)^3) :
    (A.output (parameter Z B) (by have := parameter_ge Z B;omega)).card ≤
      (Nat.log 2 ((parameter Z B)^9)+1)*(131074*(parameter Z B)^3+1) := by
  have hh := KernelBalance.output_card A (parameter Z B) (parameter_ge Z B) hW
  have hlog : Nat.log 2 ((Fintype.card W)^3)+1 ≤ Nat.log 2 ((parameter Z B)^9)+1 := by
    apply Nat.add_le_add_right
    apply Nat.log_mono_right
    simpa [← pow_mul] using Nat.pow_le_pow_left hW 3
  exact hh.trans (Nat.mul_le_mul hlog (by omega))

end GreedyShortcuts.KernelTarget
