import DirectedFlowCutGap.BinaryRetainedEntryCost

/-!
# An explicit polynomial envelope for the composed sampling charge

This is an arithmetic consequence of the actual stateful execution theorem.
Its parameter bounds the graph size, number of extra repetitions, initial
metadata width, stored trial/cutoff lengths, and the numerical trial count.
The last condition is deliberate: a short binary encoding of an arbitrarily
large trial count is not a polynomial running-time guarantee. Constructing
the confidence parameters must establish their numerical bounds separately.

No representation/callback obligation is discharged merely by these formulas;
the result bounds the same actual returned sampling increment from the entry.
-/
namespace DirectedFlowCutGap.BinarySamplingChargePolynomial
open BinaryArithmetic BinarySamplerMetadata BinaryRetainedTape BinaryRetainedTapeCost
open BinaryRetainedRoundingCost BinaryRetainedEntryCost RetainedGridState

def widthPolynomial (N : ℕ) : ℕ := N*N+N
def epochPolynomial (N : ℕ) : ℕ := N^3+2
def callbackPolynomial (N : ℕ) : ℕ := (N+1)*epochPolynomial N
def drawPolynomial (N : ℕ) : ℕ := 2*(N*N)
def deltaPolynomial (N : ℕ) : ℕ := N+widthPolynomial N+2
def ledgerPolynomial (N : ℕ) : ℕ :=
  N+callbackPolynomial N*drawPolynomial N*deltaPolynomial N
def oneCallbackPolynomial (N : ℕ) : ℕ :=
  48*(N*N+1)^2+48+drawPolynomial N*
    (2048*(N+1)*(N+widthPolynomial N+N+2)^2+
      40*(ledgerPolynomial N+(drawPolynomial N+1)*deltaPolynomial N)+
      80*(widthPolynomial N+1))
def samplingPolynomial (N : ℕ) : ℕ := callbackPolynomial N*oneCallbackPolynomial N

theorem epoch_bound {n N : ℕ} (hn : n ≤ N) : epochBudget n ≤ epochPolynomial N := by
  have hf := EncodedRoundingBounds.fuel_le_cubic n
  have hp := Nat.pow_le_pow_left hn 3
  unfold epochBudget epochPolynomial
  omega

theorem callbacks_bound {n extra N : ℕ} (hn : n ≤ N) (he : extra ≤ N) :
    totalCallbacks n extra ≤ callbackPolynomial N := by
  exact Nat.mul_le_mul (Nat.add_le_add_right he 1) (epoch_bound hn)

theorem draw_bound {n N : ℕ} (hn : n ≤ N) : drawBudget n ≤ drawPolynomial N := by
  unfold drawBudget drawPolynomial
  gcongr

theorem width_bound {n N : ℕ} {cutoff : Bits} (hn : n ≤ N) (hc : cutoff.length ≤ N) :
    boundWidth n cutoff ≤ widthPolynomial N := by
  have hm : n*n ≤ N*N := Nat.mul_le_mul hn hn
  unfold boundWidth widthPolynomial
  exact max_le (by omega) (by omega)

theorem delta_bound {n N : ℕ} {fuel cutoff : Bits}
    (hn : n ≤ N) (ht : value fuel ≤ N) (hc : cutoff.length ≤ N) :
    delta (boundWidth n cutoff) fuel ≤ deltaPolynomial N := by
  have hb := width_bound hn hc
  unfold delta deltaPolynomial
  omega

theorem ledger_bound {n extra S N : ℕ} {fuel cutoff : Bits}
    (hn : n ≤ N) (he : extra ≤ N) (hs : S ≤ N)
    (ht : value fuel ≤ N) (hc : cutoff.length ≤ N) :
    reachedWidth n fuel cutoff S (totalCallbacks n extra) ≤ ledgerPolynomial N := by
  have ha := callbacks_bound hn he
  have hd := draw_bound hn
  have hdelta := delta_bound hn ht hc
  unfold reachedWidth ledgerPolynomial
  exact Nat.add_le_add hs (Nat.mul_le_mul (Nat.mul_le_mul ha hd) hdelta)

theorem commonCharge_bound {n extra S N : ℕ} {fuel cutoff : Bits}
    (hn : n ≤ N) (he : extra ≤ N) (hs : S ≤ N)
    (ht : value fuel ≤ N) (hf : fuel.length ≤ N) (hc : cutoff.length ≤ N) :
    commonCharge n fuel cutoff S (totalCallbacks n extra) ≤ oneCallbackPolynomial N := by
  have hw := ledger_bound hn he hs ht hc
  have hd := draw_bound hn
  have hb := width_bound hn hc
  have hdelta := delta_bound hn ht hc
  have hm : n*n ≤ N*N := Nat.mul_le_mul hn hn
  unfold commonCharge callbackBound stepBound oneCallbackPolynomial
  gcongr

noncomputable section

/-- The full repeated program's increment, rather than the selected sample's
charge, obeys the displayed polynomial on the same supported execution. -/
theorem actual_sampling_bound {n L N : ℕ} [NeZero L]
    (bit : PMF Bool) (fuel cutoff : Bits) (hcut : value cutoff=L)
    (adjacency : PairFlags n) (hL : 0<L) (extra : ℕ) (s : Ledger)
    (hn : n ≤ N) (he : extra ≤ N) (hs : ledgerWidth s ≤ N)
    (ht : value fuel ≤ N) (hf : fuel.length ≤ N) (hc : cutoff.length ≤ N)
    {out : EncodedRoundingRepetition.Result n × Ledger}
    (hout : out ∈ ((EncodedRoundingRepetition.run (callback bit fuel cutoff hcut hL)
      adjacency hL extra).run s).support) :
    out.2.operations=s.operations+out.1.sampling ∧
      out.1.sampling ≤ samplingPolynomial N ∧ ledgerWidth out.2 ≤ ledgerPolynomial N := by
  have h := BinaryRetainedEntryCost.run_bound bit fuel cutoff hcut adjacency hL extra s hout
  have hK := commonCharge_bound hn he hs ht hf hc
  have hC := callbacks_bound hn he
  have hW := ledger_bound hn he hs ht hc
  exact ⟨h.2.2.1,h.2.2.2.1.trans (Nat.mul_le_mul hC hK),h.1.trans hW⟩

end
end DirectedFlowCutGap.BinarySamplingChargePolynomial
