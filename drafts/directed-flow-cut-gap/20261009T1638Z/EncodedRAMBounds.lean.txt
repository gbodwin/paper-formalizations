import Mathlib.Data.Nat.Size
import Mathlib.Tactic

/-!
# Numeric bounds for a logarithmic-cost RAM realization

These are conditional numeric helpers. They do not certify an arbitrary
program's primitive count, allocation count, or output refinement. A concrete
routine-to-instruction proof must supply those facts separately.

The fixed common width includes supplied input cells. Boolean/list allocation
is bounded first, independently of address encoding. Reading or copying an
address is then charged an additional width factor. No native compiler or
arbitrary-heap verification is asserted.
-/
namespace DirectedFlowCutGap.EncodedRAMBounds

/-- Every independent magnitude is included before selecting the common width. -/
def scale (inputCells wordBudget arithmeticBits primitiveAllowance : ℕ) : ℕ :=
  inputCells+wordBudget+arithmeticBits+primitiveAllowance+2

def commonWidth (inputCells wordBudget arithmeticBits primitiveAllowance : ℕ) : ℕ :=
  64*(scale inputCells wordBudget arithmeticBits primitiveAllowance)^2

/-- This is the allowance to be discharged by the actual primitive/allocation
certificate, not a declaration that every routine has such a realization. -/
def primitiveCells (inputCells wordBudget arithmeticBits primitiveAllowance : ℕ) : ℕ :=
  primitiveAllowance*wordBudget*
    (commonWidth inputCells wordBudget arithmeticBits primitiveAllowance+1)^2

/-- Includes initial input reads and a full address-copy/read allowance. -/
def ramTraffic (inputCells wordBudget arithmeticBits primitiveAllowance : ℕ) : ℕ :=
  (inputCells+primitiveCells inputCells wordBudget arithmeticBits primitiveAllowance)*
    (commonWidth inputCells wordBudget arithmeticBits primitiveAllowance+1)

theorem scale_two (i w b a : ℕ) : 2 ≤ scale i w b a := by unfold scale;omega

theorem scale_bounds (i w b a : ℕ) :
    i ≤ scale i w b a ∧ w ≤ scale i w b a ∧ b ≤ scale i w b a ∧ a ≤ scale i w b a := by
  unfold scale
  omega

theorem arithmetic_width (i w b a : ℕ) : b ≤ commonWidth i w b a := by
  have hb := (scale_bounds i w b a).2.2.1
  have hp := Nat.le_self_pow (by decide : 2≠0) (scale i w b a)
  unfold commonWidth
  omega

theorem width_add_one (i w b a : ℕ) :
    commonWidth i w b a+1 ≤ 65*(scale i w b a)^2 := by
  have hp := Nat.one_le_pow 2 (scale i w b a) (by have h := scale_two i w b a;omega)
  unfold commonWidth
  omega

theorem primitive_cells_polynomial (i w b a : ℕ) :
    primitiveCells i w b a ≤ 4225*(scale i w b a)^6 := by
  have hw := (scale_bounds i w b a).2.1
  have ha := (scale_bounds i w b a).2.2.2
  have hwidth := width_add_one i w b a
  calc
    primitiveCells i w b a ≤ scale i w b a*scale i w b a*(65*(scale i w b a)^2)^2 := by
      unfold primitiveCells
      gcongr
    _=4225*(scale i w b a)^6 := by ring

/-- The actual fresh-cell count remains an explicit premise. -/
theorem heap_cells_polynomial (i w b a freshCells : ℕ)
    (halloc : freshCells ≤ primitiveCells i w b a) :
    i+freshCells ≤ 4226*(scale i w b a)^6 := by
  have hi := (scale_bounds i w b a).1
  have hp := Nat.le_self_pow (by decide : 6≠0) (scale i w b a)
  have h := halloc.trans (primitive_cells_polynomial i w b a)
  omega

private theorem address_size (s address : ℕ) (hs : 2 ≤ s)
    (ha : address ≤ 4226*s^6) : address.size ≤ 64*s^2 := by
  have hpos : 0 < s^6 := pow_pos (by omega) _
  have hpow : s^6 ≤ (2^s.size)^6 :=
    Nat.pow_le_pow_left (Nat.le_of_lt (Nat.lt_size_self s)) 6
  have hlt : address < 2^(13+6*s.size) := by
    calc
      address < 8192*s^6 := by omega
      _ ≤ 8192*(2^s.size)^6 := Nat.mul_le_mul_left _ hpow
      _=2^(13+6*s.size) := by
        rw [← pow_mul,show s.size*6=6*s.size by omega,pow_add]
        norm_num
  have hb := Nat.size_le.mpr hlt
  have hn : s.size ≤ s := Nat.size_le.mpr (Nat.lt_two_pow_self)
  have hp := Nat.le_self_pow (by decide : 2≠0) s
  omega

/-- Input storage and fresh cells jointly bound every allocated address. This
is the promised noncircular width choice once halloc is actually certified. -/
theorem allocated_address_width (i w b a freshCells address : ℕ)
    (halloc : freshCells ≤ primitiveCells i w b a) (ha : address ≤ i+freshCells) :
    address.size ≤ commonWidth i w b a := by
  exact address_size (scale i w b a) address (scale_two i w b a)
    (ha.trans (heap_cells_polynomial i w b a freshCells halloc))

theorem traffic_polynomial (i w b a : ℕ) :
    ramTraffic i w b a ≤ 274690*(scale i w b a)^8 := by
  have hh := heap_cells_polynomial i w b a (primitiveCells i w b a) le_rfl
  have hw := width_add_one i w b a
  calc
    ramTraffic i w b a ≤ (4226*(scale i w b a)^6)*(65*(scale i w b a)^2) := by
      exact Nat.mul_le_mul hh hw
    _=274690*(scale i w b a)^8 := by ring

/-- An actual instruction/cell simulation must prove htraffic before this
numeric corollary can be applied to its execution. -/
theorem certified_traffic_polynomial (i w b a actualBitWork : ℕ)
    (htraffic : actualBitWork ≤ ramTraffic i w b a) :
    actualBitWork ≤ 274690*(scale i w b a)^8 :=
  htraffic.trans (traffic_polynomial i w b a)

end DirectedFlowCutGap.EncodedRAMBounds
