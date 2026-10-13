import DirectedFlowCutGap.ActualAdaptivePackingStep

namespace DirectedFlowCutGap.PackingIteration
open BinaryArithmetic BinaryRational BinaryFractionalRows

/-- Erased iteration specification. The actual controller must still execute
all fuel and state transitions; this definition supplies no machine result. -/
def repeated {n : ℕ} (capacity : Row n) (oracle : BinaryFractionalCore.Oracle n) :
    ℕ → BinaryFractionalCore.State n → BinaryFractionalCore.State n
  | 0,s => s
  | k+1,s => repeated capacity oracle k (BinaryFractionalCore.step capacity oracle s).1

theorem repeated_runFrom {n : ℕ} (capacity : Row n) (oracle : BinaryFractionalCore.Oracle n)
    (fuel : Bits) (s : BinaryFractionalCore.State n) :
    (BinaryFractionalCore.runFrom capacity oracle fuel s).state=repeated capacity oracle (value fuel) s := by
  have aux : ∀ k,∀ f : Bits,value f=k → ∀ s : BinaryFractionalCore.State n,
      (BinaryFractionalCore.runFrom capacity oracle f s).state=repeated capacity oracle k s := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro f hf s
      rw [BinaryFractionalCore.runFrom]
      split_ifs with hz
      · have hv := (isZero_spec f).1.mp hz
        have hk : k=0 := hf.symm.trans hv
        simp only [hk, repeated]
      · have hv : 0<value f := Nat.pos_of_ne_zero (fun h => hz ((isZero_spec f).1.mpr h))
        have hp := (predecessor_spec f).1
        have hm : value (predecessor f).1<k := by omega
        have ht := ih _ hm (predecessor f).1 rfl (BinaryFractionalCore.step capacity oracle s).1
        have hk : k=(value (predecessor f).1)+1 := by omega
        simpa only [hk,repeated] using ht
  exact aux (value fuel) fuel rfl s
end DirectedFlowCutGap.PackingIteration
