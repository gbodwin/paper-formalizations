import DirectedFlowCutGap.BinaryFractionalStepCost

/-!
# Fixed-fuel binary execution cost

The induction follows the actual zero-test/predecessor controller. All `3m²`
guard scans remain charged, including scans after the mathematical state stops.
The only external charge premise is explicitly about the actual oracle called
on the reached Boolean-list row. A concrete graph adapter must discharge that
premise. This theorem does not postulate an output-width certificate: widths
follow from exact-state refinement and proved canonicality.
-/
namespace DirectedFlowCutGap.BinaryFractionalLoopCost
open BinaryArithmetic BinaryRational BinaryFractionalRows BinaryFractionalCore
open BinaryFractionalCanonical BinaryFractionalWidths BinaryFractionalStepCost

variable {m : ℕ}

def loopBound (m B T R F t : ℕ) : ℕ :=
  t*(stepBound m (stateWidth m B T) R+36*(F+1)+8)+4*(F+1)+4

theorem predecessor_length (f : Bits) : (predecessor f).1.length ≤ f.length := by
  rw [(predecessor_spec f).2.1]
  apply Nat.size_le.mpr
  exact lt_of_le_of_lt (Nat.sub_le _ _) (value_lt f)

theorem runFrom_charge (c : Row m) (b : Oracle m)
    (r : FractionalCoverRawCore.RawOracle m) (ho : Refines b r)
    (B T R F : ℕ) (hc : RowStored c B)
    (horacle : ∀ y, RowStored y (stateWidth m B T) → (b y).2 ≤ R)
    (fuel : Bits) (s : State m) (k : ℕ)
    (hs : StateCanonical s)
    (hr : decodeState s = FractionalCoverRawCore.run (decodeRow c) r k)
    (hT : k+value fuel ≤ T) (hF : fuel.length ≤ F) :
    (runFrom c b fuel s).operations ≤ loopBound m B T R F (value fuel) := by
  have aux : ∀ t, ∀ f : Bits, value f=t → ∀ s : State m, ∀ k,
      StateCanonical s →
      decodeState s = FractionalCoverRawCore.run (decodeRow c) r k →
      k+value f ≤ T → f.length ≤ F →
      (runFrom c b f s).operations ≤ loopBound m B T R F (value f) := by
    intro t
    induction t using Nat.strong_induction_on with
    | h t ih =>
      intro f hf s k hcan hraw htotal hlen
      have hz := (isZero_spec f).2
      rw [runFrom]
      split_ifs with hzero
      · have hv := (isZero_spec f).1.mp hzero
        simp only [loopBound,hv,zero_mul,zero_add]
        omega
      · have hv : 0<value f := Nat.pos_of_ne_zero
          (fun he => hzero ((isZero_spec f).1.mpr he))
        have hp := predecessor_spec f
        have hnextcan := step_canonical c b s hcan
        have hnextraw : decodeState (step c b s).1 =
            FractionalCoverRawCore.run (decodeRow c) r (k+1) := by
          rw [step_refines c b r ho,hraw]
          rfl
        have hnext := ih (value (predecessor f).1) (by rw [hp.1,← hf];omega)
          (predecessor f).1 rfl (step c b s).1 (k+1) hnextcan hnextraw
          (by rw [hp.1];omega) ((predecessor_length f).trans hlen)
        have hstate := state_stored_of_raw c r s B k hc hcan hraw
        have hmono := stateWidth_mono m B (show k ≤ T by omega)
        have hwide : StateStored s (stateWidth m B T) :=
          ⟨rowStored_mono hstate.weights hmono,rowStored_mono hstate.best hmono,
            stored_mono hstate.bestCost hmono,stored_mono hstate.total hmono,
            rowStored_mono hstate.loads hmono⟩
        have hinput := rowStored_mono hc (width_bounds m B T).2.2.2.2
        have hstep := step_charge c b s (stateWidth m B T) R hinput hwide
          (horacle s.weights hwide.weights)
        dsimp only
        unfold loopBound at hnext ⊢
        rw [hp.1] at hnext
        have he : value f=(value f-1)+1 := by omega
        rw [he,Nat.add_mul]
        nlinarith [hp.2.2]
  exact aux _ fuel rfl s k hs hr hT hF

end DirectedFlowCutGap.BinaryFractionalLoopCost
