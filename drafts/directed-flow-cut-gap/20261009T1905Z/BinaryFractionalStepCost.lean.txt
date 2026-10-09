import DirectedFlowCutGap.BinaryFractionalWidths

/-!
# Charges of the actual binary covering step

Every scalar charge below comes from the Boolean-list arithmetic execution.
The objective guard is charged on stopped states as well. The oracle's actual
returned charge is left explicit; a concrete graph adapter must prove that
charge bound separately. Array constructors use their existing charged scans;
their fixed-body cost-semantics certificate remains a separate layer.
-/
namespace DirectedFlowCutGap.BinaryFractionalStepCost
open BinaryRational BinaryFractionalRows BinaryFractionalCore BinaryFractionalWidths
open EncodedRoundingInput

variable {m : ℕ}

theorem stored_mono {a : Fraction} {A B : ℕ} (h : StoredBounded a A) (hab : A ≤ B) :
    StoredBounded a B := ⟨h.1.trans hab,h.2.trans hab⟩

theorem normalized_stored (y : Row m) (mask : Vector Bool m) (B : ℕ)
    (hy : RowStored y B) :
    RowStored (normalized y mask).1 ((m+1)*(B+1)+1) := by
  intro i
  have h := FractionalCoverRawCore.normalizedCode_bounded (row_raw hy) (column mask) i
  rw [← normalized_decode] at h
  simp only [decode_get] at h
  have hc := BinaryFractionalCanonical.normalized_canonical y mask i
  have hs := BinaryFractionalCanonical.stored_of_raw hc h
  apply stored_mono hs
  unfold FractionalCoverRawCore.normalWidth
  nlinarith

def updateBound (m B : ℕ) : ℕ :=
  m*(factorBound B+2048*(2*B+4)^2+8)+arrayBound m

theorem update_charge (c y : Row m) (mask : Vector Bool m) (j : Fin m) (B : ℕ)
    (hc : RowStored c B) (hy : RowStored y B) :
    (update c y mask j).2 ≤ updateBound m B := by
  apply tabulate_bound
  intro i
  split
  · have hf := factor_charge c i j B hc
    have hs := factor_stored c i j B hc
    have hm := mul_charge (stored_mono (hy i) (by omega : B ≤ 2*B+3)) hs
    rw [show 2*B+3+1=2*B+4 by omega] at hm
    dsimp only
    omega
  · dsimp only
    unfold factorBound
    omega

def loadsBound (m B : ℕ) : ℕ := m*(2048*(B+2)^2+5)+arrayBound m

theorem loads_charge (loads : Row m) (mask : Vector Bool m) (amount : Fraction)
    (B : ℕ) (hy : RowStored loads B) (ha : StoredBounded amount B) :
    (addLoads loads mask amount).2 ≤ loadsBound m B := by
  apply tabulate_bound
  intro i
  have hterm : StoredBounded (if mask[i.val] then amount else zero) (B+1) := by
    split
    · exact stored_mono ha (Nat.le_succ B)
    · simp [StoredBounded,zero]
  exact Nat.add_le_add_right
    (add_charge (stored_mono (hy i) (Nat.le_succ B)) hterm) 5

def scalarWidth (m B : ℕ) : ℕ := (m+1)^2*(4*B+8)

theorem scalar_width_bounds (m B : ℕ) :
    B ≤ scalarWidth m B ∧ 1 ≤ scalarWidth m B ∧
    m*(2*B+1)+1 ≤ scalarWidth m B ∧
    (m+1)*(B+1)+1 ≤ scalarWidth m B ∧
    m*(2*((m+1)*(B+1)+1)+1)+1 ≤ scalarWidth m B := by
  unfold scalarWidth
  constructor
  · nlinarith [Nat.zero_le (m*m*B),Nat.zero_le (m*B)]
  constructor
  · nlinarith [Nat.zero_le (m*m*B),Nat.zero_le (m*B)]
  constructor
  · nlinarith [Nat.zero_le (m*m*B),Nat.zero_le (m*B)]
  constructor <;> nlinarith [Nat.zero_le (m*m*B),Nat.zero_le (m*B)]

/-- The expression is polynomial in dimension and maximum stored scalar width.
The oracle charge is an additive parameter, rather than a free primitive. -/
def stepBound (m B R : ℕ) : ℕ :=
  objectiveBound m B + 4096*(scalarWidth m B+1)^2 + R + normalizedBound m B +
  objectiveBound m ((m+1)*(B+1)+1) + updateBound m B +
  2048*(B+1)^2 + loadsBound m B + 28

theorem step_charge (c : Row m) (oracle : Oracle m) (s : State m) (B R : ℕ)
    (hc : RowStored c B) (hs : StateStored s B)
    (ho : (oracle s.weights).2 ≤ R) :
    (step c oracle s).2 ≤ stepBound m B R := by
  let K := scalarWidth m B
  have hw := scalar_width_bounds m B
  have hd := objective_charge c s.weights B hc hs.weights
  have hds := objective_stored c s.weights B hc hs.weights
  have hone : StoredBounded one K := by
    exact stored_mono (by simp [StoredBounded,one] : StoredBounded one 1) hw.2.1
  have hstop := le_charge hone (stored_mono hds hw.2.2.1)
  have hn := normalized_charge s.weights (oracle s.weights).1.mask B hs.weights
  have hns := normalized_stored s.weights (oracle s.weights).1.mask B hs.weights
  have hbN : B ≤ (m+1)*(B+1)+1 := by nlinarith
  have hcan := objective_charge c
    (normalized s.weights (oracle s.weights).1.mask).1 ((m+1)*(B+1)+1)
    (rowStored_mono hc hbN) hns
  have hcans := objective_stored c
    (normalized s.weights (oracle s.weights).1.mask).1 ((m+1)*(B+1)+1)
    (rowStored_mono hc hbN) hns
  have hcmp := le_charge (stored_mono hs.bestCost hw.1)
    (stored_mono hcans hw.2.2.2.2)
  have hup := update_charge c s.weights (oracle s.weights).1.mask
    (oracle s.weights).1.bottleneck B hc hs.weights
  have htotal := add_charge hs.total (hc (oracle s.weights).1.bottleneck)
  have hloads := loads_charge s.loads (oracle s.weights).1.mask
    (get c (oracle s.weights).1.bottleneck) B hs.loads
    (hc (oracle s.weights).1.bottleneck)
  unfold step
  dsimp only
  split
  · unfold stepBound
    dsimp [K] at hstop
    omega
  · unfold stepBound
    dsimp [K] at hstop hcmp
    omega

end DirectedFlowCutGap.BinaryFractionalStepCost
