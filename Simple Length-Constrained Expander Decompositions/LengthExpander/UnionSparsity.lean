import LengthExpander.UnionWitness
import LengthExpander.DecompositionReduction

/-! The repaired union-sparsity theorem, with the positive denominator and
all finite-copy/integrality losses explicit. The constant is
16*(ceil(8s(2|A|)^(2/s))+1), of the advertised asymptotic order. -/
namespace LengthExpander
open Finset SimpleGraph
attribute [local instance] Classical.propDecidable
variable {V : Type*} [Fintype V]

theorem cutCost_total_eq_sum (G : SimpleGraph V) (U : Sym2 V → ℕ)
    (Cs : List (EdgeLength V)) :
    cutCost G U (totalCut Cs) = (Cs.map (cutCost G U)).sum := by
  induction Cs with
  | nil => simp
  | cons C Cs ih => simp only [totalCut_cons,cutCost_add,List.map_cons,List.sum_cons,ih]

theorem rescaling_le_two {s : ℕ} (hs : 2 ≤ s) : 1+1/((s:ℝ)-1) ≤ 2 := by
  have hs' : (2:ℝ) ≤ s := by exact_mod_cast hs
  have hp : (0:ℝ) < (s:ℝ)-1 := by linarith
  have hd : (1:ℝ)/((s:ℝ)-1) ≤ 1 := (div_le_one hp).mpr (by linarith)
  linarith

/-- Theorem 4.1/1.4 in the finite integer-s regime. A zero total witness
volume is explicitly excluded rather than assigned a totalized sparsity ratio. -/
theorem union_sparseCut (G : SimpleGraph V) (U : Sym2 V → ℕ) (A : NodeWeight V)
    (w : EdgeLength V) (h : ℝ) (s : ℕ) (Cs : List (EdgeLength V))
    (hCs : NonnegativeCuts Cs) (hh : 0 ≤ h) (hs : 2 ≤ s)
    (hvol : 0 < sequenceVolume G A h s w Cs) :
    SparseCut G U w A (2*h) (((s:ℝ)-1)/2)
      (16*(densityBudget (2*weightSize A) s+1:ℕ)*cutCost G U (totalCut Cs) /
        (sequenceVolume G A h s w Cs : ℝ)) (unionCut Cs s) := by
  classical
  obtain ⟨D,hD,hm⟩ := exists_union_witness G A w h s Cs hCs hh hs
  let K := densityBudget (2*weightSize A) s+1
  have hDpos : 0 < demandSize D := by
    by_contra hz
    have hz' : demandSize D = 0 := by omega
    rw [hz',mul_zero] at hm
    omega
  have hVolume := witness_size_le_volume hD
  have hvpos : 0 < demandVolume G w (unionCut Cs s) A (2*h) (((s:ℝ)-1)/2) := hDpos.trans_le hVolume
  have hN : (0:ℝ) < sequenceVolume G A h s w Cs := by exact_mod_cast hvol
  have hn : (sequenceVolume G A h s w Cs : ℝ) ≤
      8*(K:ℝ)*demandVolume G w (unionCut Cs s) A (2*h) (((s:ℝ)-1)/2) := by
    exact_mod_cast hm.trans (Nat.mul_le_mul_left _ hVolume)
  have hcost0 := cutCost_nonneg G U (nonnegativeCuts_total hCs)
  have hs' : (2:ℝ) ≤ s := by exact_mod_cast hs
  have hq : (0:ℝ) ≤ 1+1/((s:ℝ)-1) := (by norm_num : (0:ℝ) ≤ 1).trans (rescaling_ge_one hs')
  have hc : cutCost G U (unionCut Cs s) ≤ 2*cutCost G U (totalCut Cs) := by
    unfold unionCut
    rw [cutCost_scale]
    exact mul_le_mul_of_nonneg_right (rescaling_le_two hs) hcost0
  refine ⟨fun e => mul_nonneg hq (nonnegativeCuts_total hCs e),hvpos,?_⟩
  have hb : cutCost G U (unionCut Cs s) * (sequenceVolume G A h s w Cs : ℝ) ≤
      (16*(K:ℝ)*cutCost G U (totalCut Cs)) *
        demandVolume G w (unionCut Cs s) A (2*h) (((s:ℝ)-1)/2) := by
    calc
      _ ≤ (2*cutCost G U (totalCut Cs)) * (sequenceVolume G A h s w Cs : ℝ) :=
        mul_le_mul_of_nonneg_right hc hN.le
      _ ≤ (2*cutCost G U (totalCut Cs)) *
          (8*(K:ℝ)*demandVolume G w (unionCut Cs s) A (2*h) (((s:ℝ)-1)/2)) :=
        mul_le_mul_of_nonneg_left hn (mul_nonneg (by norm_num) hcost0)
      _ = _ := by ring
  have hb' := (le_div_iff₀ hN).mpr hb
  convert hb' using 1 <;> (try dsimp [K]) <;> ring

end LengthExpander
