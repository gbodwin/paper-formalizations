import LengthExpander.RealUnionWitness
import LengthExpander.DecompositionReduction

/-! A valid all-real union-sparsity theorem, retaining exact real cut
geometry and using the floor threshold only for auxiliary graph density. -/
namespace LengthExpander
open Finset SimpleGraph
attribute [local instance] Classical.propDecidable
variable {V : Type*} [Fintype V]

theorem real_rescaling_le_two {s : ℝ} (hs : 2 ≤ s) : 1+1/(s-1) ≤ 2 := by
  have hp : (0:ℝ) < s-1 := by linarith
  have hd : (1:ℝ)/(s-1) ≤ 1 := (div_le_one hp).mpr (by linarith)
  linarith

/-- Rounded all-real union bound. A zero total witness
volume is explicitly excluded rather than assigned a totalized sparsity ratio. -/
theorem real_union_sparseCut (G : SimpleGraph V) (U : Sym2 V → ℕ) (A : NodeWeight V)
    (w : EdgeLength V) (h s : ℝ) (Cs : List (EdgeLength V))
    (hCs : NonnegativeCuts Cs) (hh : 0 ≤ h) (hs : 2 ≤ s)
    (hvol : 0 < sequenceVolume G A h s w Cs) :
    SparseCut G U w A (2*h) ((s-1)/2)
      (16*(densityBudget (2*weightSize A) ⌊s⌋₊+1:ℕ)*cutCost G U (totalCut Cs) /
        (sequenceVolume G A h s w Cs : ℝ)) (realUnionCut Cs s) := by
  classical
  obtain ⟨D,hD,hm⟩ := exists_real_union_witness G A w h s Cs hCs hh hs
  let K := densityBudget (2*weightSize A) ⌊s⌋₊+1
  have hDpos : 0 < demandSize D := by
    by_contra hz
    have hz' : demandSize D = 0 := by omega
    rw [hz',mul_zero] at hm
    omega
  have hVolume := witness_size_le_volume hD
  have hvpos : 0 < demandVolume G w (realUnionCut Cs s) A (2*h) ((s-1)/2) := hDpos.trans_le hVolume
  have hN : (0:ℝ) < sequenceVolume G A h s w Cs := by exact_mod_cast hvol
  have hn : (sequenceVolume G A h s w Cs : ℝ) ≤
      8*(K:ℝ)*demandVolume G w (realUnionCut Cs s) A (2*h) ((s-1)/2) := by
    exact_mod_cast hm.trans (Nat.mul_le_mul_left _ hVolume)
  have hcost0 := cutCost_nonneg G U (nonnegativeCuts_total hCs)
  have hq : (0:ℝ) ≤ 1+1/(s-1) := (by norm_num : (0:ℝ) ≤ 1).trans (rescaling_ge_one hs)
  have hc : cutCost G U (realUnionCut Cs s) ≤ 2*cutCost G U (totalCut Cs) := by
    unfold realUnionCut
    rw [cutCost_scale]
    exact mul_le_mul_of_nonneg_right (real_rescaling_le_two hs) hcost0
  refine ⟨fun e => mul_nonneg hq (nonnegativeCuts_total hCs e),hvpos,?_⟩
  have hb : cutCost G U (realUnionCut Cs s) * (sequenceVolume G A h s w Cs : ℝ) ≤
      (16*(K:ℝ)*cutCost G U (totalCut Cs)) *
        demandVolume G w (realUnionCut Cs s) A (2*h) ((s-1)/2) := by
    calc
      _ ≤ (2*cutCost G U (totalCut Cs)) * (sequenceVolume G A h s w Cs : ℝ) :=
        mul_le_mul_of_nonneg_right hc hN.le
      _ ≤ (2*cutCost G U (totalCut Cs)) *
          (8*(K:ℝ)*demandVolume G w (realUnionCut Cs s) A (2*h) ((s-1)/2)) :=
        mul_le_mul_of_nonneg_left hn (mul_nonneg (by norm_num) hcost0)
      _ = _ := by ring
  have hb' := (le_div_iff₀ hN).mpr hb
  convert hb' using 1 <;> (try dsimp [K]) <;> ring

theorem real_union_loss_bound {N : ℕ} {s : ℝ} (hN : 0 < N) (hs : 2 ≤ s) :
    (16:ℝ)*(densityBudget (2*N) ⌊s⌋₊+1:ℕ) ≤ 512*s*(N:ℝ)^(4/s) := by
  have hi := union_loss_bound hN (floor_threshold_bounds hs).1
  have hr := rounded_density_le_smooth N hs
  nlinarith

/-- All-real repaired Theorem 4.1, with exponent 4/s and the original
real separation threshold. Positive input volume remains explicit. -/
theorem real_union_sparseCut_explicit (G : SimpleGraph V) (U : Sym2 V → ℕ)
    (A : NodeWeight V) (w : EdgeLength V) (h s : ℝ) (Cs : List (EdgeLength V))
    (hCs : NonnegativeCuts Cs) (hh : 0 ≤ h) (hs : 2 ≤ s)
    (hvol : 0 < sequenceVolume G A h s w Cs) :
    SparseCut G U w A (2*h) ((s-1)/2)
      (512*s*(weightSize A:ℝ)^(4/s)*cutCost G U (totalCut Cs) /
        (sequenceVolume G A h s w Cs:ℝ)) (realUnionCut Cs s) := by
  have hc := real_union_sparseCut G U A w h s Cs hCs hh hs hvol
  have hA : 0 < weightSize A := hc.2.1.trans_le
    (volume_le_weightSize G w (realUnionCut Cs s) A (2*h) ((s-1)/2))
  have hl := real_union_loss_bound hA hs
  have hcost := cutCost_nonneg G U (nonnegativeCuts_total hCs)
  have hphi := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hl hcost)
    (Nat.cast_nonneg (sequenceVolume G A h s w Cs))
  exact ⟨hc.1,hc.2.1,hc.2.2.trans (mul_le_mul_of_nonneg_right hphi (Nat.cast_nonneg _))⟩

end LengthExpander
