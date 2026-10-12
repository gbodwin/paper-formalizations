import GreedyShortcuts.PathFourHeight

/-! The proved four-hop construction with an executable ceiling-log height.
The height program descends in m without searching or materializing a power
tower. The witness retains the existing lower-tower block-size computation. -/
namespace GreedyShortcuts.PathFour

theorem clog_lt_input {m : ℕ} (hm : 2<m) : Nat.clog 2 m<m := by
  have hp := Nat.lt_two_pow_self (n:=m-1)
  have hc : Nat.clog 2 m≤m-1 := (Nat.clog_le_iff_le_pow (by decide)).mpr (by omega)
  omega

def computedHeight (m : ℕ) : ℕ :=
  if hm : 2<m then computedHeight (Nat.clog 2 m)+1 else 0
termination_by m
decreasing_by exact clog_lt_input hm

theorem computedHeight_eq (m : ℕ) : computedHeight m=height m := by
  rw [computedHeight]
  split_ifs with hm
  · rw [computedHeight_eq (Nat.clog 2 m),height_clog hm]
  · exact (height_zero (by omega)).symm
termination_by m
decreasing_by exact clog_lt_input hm

def computedWitness (m : ℕ) : ChainUnion.PathWitness m (6*computedHeight m+1) :=
  towerWitness (computedHeight m) m (by rw [computedHeight_eq];exact height_spec m)

end GreedyShortcuts.PathFour
