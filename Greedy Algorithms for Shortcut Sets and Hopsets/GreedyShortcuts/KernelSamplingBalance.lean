import GreedyShortcuts.KernelSamples
import GreedyShortcuts.KernelTarget

/-! Concrete deterministic kernel balancing. Only explicit numerical regime
conditions remain; no geometric kernel witness is supplied by the caller. -/
namespace GreedyShortcuts.KernelSamplingBalance
open DirectedPaths
variable {V : Type*} [Fintype V] [DecidableEq V]

def logarithm (n : ℕ) : ℕ := Nat.log 2 (n^2)+1
def radius (n b : ℕ) : ℕ := 2*logarithm n*n/b^3

theorem sample_budget (n b : ℕ) (hb : 0<b) (hk : 2*logarithm n ≤ b^3) :
    logarithm n*(n/(radius n b+1)+1) ≤ b^3 := by
  let k := logarithm n
  let r := radius n b
  have hb3 : 0<b^3 := by positivity
  have hrpos : 0<r+1 := by omega
  have hnum : 2*k*n < b^3*(r+1) := by
    have hrem := Nat.mod_lt (2*k*n) hb3
    have he := Nat.mod_add_div (2*k*n) (b^3)
    change 2*k*n < b^3*(2*k*n/b^3+1)
    nlinarith
  have hquot := Nat.div_mul_le_self n (r+1)
  have hd : 2*k*(n/(r+1)) < b^3 := by
    nlinarith
  change k*(n/(r+1)+1) ≤ b^3
  change 2*k ≤ b^3 at hk
  nlinarith

theorem scale (n b : ℕ) (hbn : b^3 ≤ logarithm n*n) :
    (2*radius n b+2)*b^3 ≤ 6*logarithm n*n := by
  have hq := Nat.div_mul_le_self (2*logarithm n*n) (b^3)
  unfold radius
  nlinarith

noncomputable def output (G : V → V → Prop) (b : ℕ) (hb : 1≤b) : Finset (V × V) :=
  (KernelSamples.sampleKernel G (radius (Fintype.card V) b)).output b hb

theorem output_legal (G : V → V → Prop) (b : ℕ) (hb : 1≤b) :
    output G b hb ⊆ candidates G := (KernelSamples.sampleKernel G _).output_legal b hb

theorem output_card (G : V → V → Prop) (b : ℕ) (hb : 8≤b)
    (hk : 2*logarithm (Fintype.card V) ≤ b^3) :
    (output G b (by omega)).card ≤ (Nat.log 2 (b^9)+1)*(131074*b^3+1) := by
  let r := radius (Fintype.card V) b
  have hS : Fintype.card (KernelSamples.samples G r) ≤ b^3 := by
    simpa only [Fintype.card_coe] using
      (KernelSamples.samples_card_le G r).trans (sample_budget (Fintype.card V) b (by omega) hk)
  have hh := KernelBalance.output_card (KernelSamples.sampleKernel G r) b hb hS
  have hl : Nat.log 2 ((Fintype.card (KernelSamples.samples G r))^3)+1 ≤
      Nat.log 2 (b^9)+1 := by
    apply Nat.add_le_add_right
    apply Nat.log_mono_right
    simpa [← pow_mul] using Nat.pow_le_pow_left hS 3
  exact hh.trans (Nat.mul_le_mul hl (by omega))

theorem output_hop_scaled (G : V → V → Prop) (b : ℕ) (hb : 1≤b)
    (hbn : b^3 ≤ logarithm (Fintype.card V)*Fintype.card V)
    {s t : V} (hr : Reachable G s t) :
    hopDist (augment G (output G b hb)) s t*b^2 ≤
      42*logarithm (Fintype.card V)*Fintype.card V := by
  have hh := KernelBalance.output_hop_scaled
    (KernelSamples.sampleKernel G (radius (Fintype.card V) b)) b hb (by omega) (by omega)
    (6*logarithm (Fintype.card V)*Fintype.card V) (scale (Fintype.card V) b hbn) hr
  calc
    _ ≤ 7*(6*logarithm (Fintype.card V)*Fintype.card V) := hh
    _ = _ := by ring

theorem output_hop (G : V → V → Prop) (b B : ℕ) (hb : 1≤b)
    (hbn : b^3 ≤ logarithm (Fintype.card V)*Fintype.card V)
    (hB : 42*logarithm (Fintype.card V)*Fintype.card V ≤ B*b^2)
    {s t : V} (hr : Reachable G s t) :
    hopDist (augment G (output G b hb)) s t ≤ B :=
  Nat.le_of_mul_le_mul_right ((output_hop_scaled G b hb hbn hr).trans hB) (by positivity)

def parameter (n B : ℕ) : ℕ := max (8+2*logarithm n) (Nat.sqrt (42*logarithm n*n/B)+1)

theorem parameter_ge (n B : ℕ) : 8 ≤ parameter n B :=
  (by omega : 8 ≤ 8+2*logarithm n).trans (Nat.le_max_left _ _)

theorem parameter_budget (n B : ℕ) : 2*logarithm n ≤ (parameter n B)^3 := by
  have hp : 2*logarithm n ≤ parameter n B :=
    (by omega : 2*logarithm n ≤ 8+2*logarithm n).trans (Nat.le_max_left _ _)
  have hb := parameter_ge n B
  nlinarith [Nat.pow_le_pow_left (by omega : 1 ≤ parameter n B) 2]

theorem parameter_target (n B : ℕ) (hB : 0<B) :
    42*logarithm n*n ≤ B*(parameter n B)^2 := by
  have hp : KernelTarget.parameter (6*logarithm n*n) B ≤ parameter n B := by
    unfold KernelTarget.parameter parameter
    apply max_le
    · exact (by omega : 8 ≤ 8+2*logarithm n).trans (Nat.le_max_left _ _)
    · have he : 7*(6*logarithm n*n) = 42*logarithm n*n := by ring
      rw [he]
      exact Nat.le_max_right _ _
  have ht := KernelTarget.target_square (6*logarithm n*n) B hB
  have hm := Nat.mul_le_mul_left B (Nat.pow_le_pow_left hp 2)
  nlinarith

/-- A concrete, geometrically unconditional target theorem in the explicit
numerical range. The remaining range split is not hidden in a kernel input. -/
theorem target_hop (G : V → V → Prop) (B : ℕ) (hB : 0<B)
    (hregime : (parameter (Fintype.card V) B)^3 ≤ logarithm (Fintype.card V)*Fintype.card V)
    {s t : V} (hr : Reachable G s t) :
    hopDist (augment G (output G (parameter (Fintype.card V) B)
      (by have := parameter_ge (Fintype.card V) B;omega))) s t ≤ B :=
  output_hop G _ B _ hregime (parameter_target _ B hB) hr

end GreedyShortcuts.KernelSamplingBalance
