import VFTSpanners.PaperTheorem
import VFTSpanners.Moore

namespace VFTSpanners
open SimpleGraph
open scoped ENNReal
attribute [local instance] Classical.propDecidable

/-- Modular statement of the Moore bound, written without real powers.
`mooreBound_two` below supplies a proof with uniform constant `2`. -/
def MooreBound (r C : ℕ) : Prop :=
  ∀ n, (extremalEdges n (2*r))^r ≤ C^r*n^(r+1)

/-- Algebra behind Corollary 2 in the sampling regime. -/
theorem moore_substitution (n m f r C : ℕ) (hf : 1 ≤ f) (hr : 1 ≤ r)
    (hn : 2*f ≤ n) (hMoore : MooreBound r C)
    (hm : m ≤ 36*f^2*extremalEdges (max 2 (n/f)) (2*r)) :
    m^r ≤ (36*C)^r*n^(r+1)*f^(r-1) := by
  have hN : 2 ≤ n/f := (Nat.le_div_iff_mul_le (by omega)).mpr hn
  rw [max_eq_right hN] at hm
  have hexp : 2*r = (r-1)+(r+1) := by omega
  calc
    m^r ≤ (36*f^2*extremalEdges (n/f) (2*r))^r := Nat.pow_le_pow_left hm r
    _ = 36^r*f^(2*r)*(extremalEdges (n/f) (2*r))^r := by
      simp only [mul_pow, ← pow_mul]
    _ ≤ 36^r*f^(2*r)*(C^r*(n/f)^(r+1)) :=
      Nat.mul_le_mul_left _ (hMoore (n/f))
    _ = (36*C)^r*f^(r-1)*((n/f)*f)^(r+1) := by
      rw [hexp, pow_add]
      simp only [mul_pow]
      ring
    _ ≤ (36*C)^r*f^(r-1)*n^(r+1) :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (Nat.div_mul_le_self n f) (r+1))
    _ = _ := by ring

/-- The elementary dense-fault case needed for the conditional corollary. -/
theorem dense_fault_power_bound (n m f r C : ℕ) (hr : 1 ≤ r) (hC : 1 ≤ C)
    (hn : n ≤ 2*f) (hm : m ≤ n^2) :
    m^r ≤ (36*C)^r*n^(r+1)*f^(r-1) := by
  have hexp : 2*r = (r+1)+(r-1) := by omega
  have hcoef : 2^(r-1) ≤ (36*C)^r := by
    exact (Nat.pow_le_pow_left (by omega : 2 ≤ 36*C) (r-1)).trans
      (Nat.pow_le_pow_right (by omega : 0 < 36*C) (Nat.sub_le r 1))
  calc
    m^r ≤ (n^2)^r := Nat.pow_le_pow_left hm r
    _ = n^(r+1)*n^(r-1) := by rw [← pow_mul,hexp,pow_add]
    _ ≤ n^(r+1)*(2*f)^(r-1) :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hn (r-1))
    _ = 2^(r-1)*n^(r+1)*f^(r-1) := by rw [mul_pow]; ring
    _ ≤ (36*C)^r*n^(r+1)*f^(r-1) :=
      Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hcoef)

/-- Corollary 2 conditional on an explicit Moore bound, in equivalent
integer-power form: `m^r ≤ (36 C)^r n^(r+1) f^(r-1)` for stretch `2r-1`.
This modular version accepts any proved constant `C`; `corollary_two` below
discharges the premise with `C = 2`. -/
theorem corollary_two_from_moore {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (w : Sym2 V → ℝ) (r f C : ℕ)
    (hr : 1 ≤ r) (hf : 1 ≤ f) (hC : 1 ≤ C) (hw : ∀ e, 0 ≤ w e)
    (hMoore : MooreBound r C) :
    (greedyOutput G w (2*r-1) f).edgeFinset.card^r ≤
      (36*C)^r*(Fintype.card V)^(r+1)*f^(r-1) := by
  by_cases hn : 2*f ≤ Fintype.card V
  · obtain ⟨_,_,hsize⟩ := vft_greedy_theorem_one G w (2*r-1) f (by omega) hf hw
    have heq : 2*r-1+1 = 2*r := by omega
    rw [heq] at hsize
    exact moore_substitution _ _ _ _ _ hf hr hn hMoore hsize
  · apply dense_fault_power_bound _ _ _ _ _ hr hC (by omega)
    have hc := (greedyOutput G w (2*r-1) f).card_edgeFinset_le_card_choose_two
    rw [Nat.choose_two_right] at hc
    have hd := Nat.div_le_self (Fintype.card V * (Fintype.card V - 1)) 2
    have hp := Nat.mul_le_mul_left (Fintype.card V) (Nat.sub_le (Fintype.card V) 1)
    nlinarith

/-- The proved Moore bound discharges the modular corollary's premise. -/
theorem mooreBound_two (r : ℕ) (hr : 1 ≤ r) : MooreBound r 2 :=
  fun n => extremalEdges_moore n r hr

/-- Unconditional size bound in Corollary 2, with uniform constant `72`. -/
theorem corollary_two_size {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (w : Sym2 V → ℝ) (r f : ℕ)
    (hr : 1 ≤ r) (hf : 1 ≤ f) (hw : ∀ e, 0 ≤ w e) :
    (greedyOutput G w (2*r-1) f).edgeFinset.card^r ≤
      72^r*(Fintype.card V)^(r+1)*f^(r-1) := by
  simpa using corollary_two_from_moore G w r f 2 hr hf (by omega) hw
    (mooreBound_two r hr)

/-- Corollary 2, VFT setting, with no assumed extremal bound. The actual
weighted greedy output is a subgraph, preserves all surviving distances
within stretch `2*r-1` after at most `f` vertex faults, and satisfies the
paper's size bound in integer-power form. -/
theorem corollary_two {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (w : Sym2 V → ℝ) (r f : ℕ)
    (hr : 1 ≤ r) (hf : 1 ≤ f) (hw : ∀ e, 0 ≤ w e) :
    greedyOutput G w (2*r-1) f ≤ G ∧
      (∀ F : Finset V, F.card ≤ f → ∀ u v,
        faultDistance (greedyOutput G w (2*r-1) f) w F u v ≤
          ((2*r-1 : ℕ) : ℝ≥0∞)*faultDistance G w F u v) ∧
      (greedyOutput G w (2*r-1) f).edgeFinset.card^r ≤
        72^r*(Fintype.card V)^(r+1)*f^(r-1) := by
  obtain ⟨hs,hd,_⟩ := vft_greedy_theorem_one G w (2*r-1) f (by omega) hf hw
  exact ⟨hs,hd,corollary_two_size G w r f hr hf hw⟩

end VFTSpanners
