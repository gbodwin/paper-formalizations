import LengthExpander.Demands
import LengthExpander.Metric
import Mathlib.Data.Nat.Find
import Mathlib.Data.Finset.Card

/-! Definitions 2.5--2.13 with zero-demand and degenerate conventions explicit. -/
namespace LengthExpander
open Finset SimpleGraph
variable {V : Type*} [Fintype V]

noncomputable def cutCost (G : SimpleGraph V) (U : Sym2 V → ℕ)
    (C : EdgeLength V) : ℝ := by
  classical
  exact ∑ e ∈ G.edgeFinset, (U e : ℝ) * C e

theorem cutCost_nonneg (G : SimpleGraph V) (U : Sym2 V → ℕ)
    {C : EdgeLength V} (hC : ∀ e, 0 ≤ C e) : 0 ≤ cutCost G U C := by
  classical
  exact sum_nonneg fun e _ => mul_nonneg (Nat.cast_nonneg _) (hC e)

theorem cutCost_add (G : SimpleGraph V) (U : Sym2 V → ℕ) (C D : EdgeLength V) :
    cutCost G U (fun e => C e + D e) = cutCost G U C + cutCost G U D := by
  classical
  simp [cutCost, mul_add, sum_add_distrib]

@[simp] theorem cutCost_zero (G : SimpleGraph V) (U : Sym2 V → ℕ) :
    cutCost G U (fun _ => 0) = 0 := by
  classical
  simp [cutCost]

/-- A demand witnessing volume: bounded node budgets, h-near in the input,
and strictly hs-far after applying the cut at scale hs. -/
def CutWitness (G : SimpleGraph V) (w C : EdgeLength V) (A : NodeWeight V)
    (h s : ℝ) (D : Demand V) : Prop :=
  Respects D A ∧
  (∀ u v, 0 < D u v → Near G w h u v) ∧
  (∀ u v, 0 < D u v → Far G (applyCut w C (h*s)) (h*s) u v)

theorem zero_cutWitness (G : SimpleGraph V) (w C : EdgeLength V)
    (A : NodeWeight V) (h s : ℝ) : CutWitness G w C A h s (fun _ _ => 0) := by
  exact ⟨respects_zero A, by simp, by simp⟩

/-- The maximum is attained: integral budgets make the witness sizes finite. -/
noncomputable def demandVolume (G : SimpleGraph V) (w C : EdgeLength V)
    (A : NodeWeight V) (h s : ℝ) : ℕ := by
  classical
  exact Nat.findGreatest (fun n => ∃ D, CutWitness G w C A h s D ∧ demandSize D = n)
    (weightSize A)

theorem exists_volume_witness (G : SimpleGraph V) (w C : EdgeLength V)
    (A : NodeWeight V) (h s : ℝ) :
    ∃ D, CutWitness G w C A h s D ∧ demandSize D = demandVolume G w C A h s := by
  classical
  exact Nat.findGreatest_spec
    (P := fun n => ∃ D, CutWitness G w C A h s D ∧ demandSize D = n)
    (Nat.zero_le (weightSize A))
    ⟨fun _ _ => 0, zero_cutWitness G w C A h s, by simp [demandSize]⟩

theorem volume_le_weightSize (G : SimpleGraph V) (w C : EdgeLength V)
    (A : NodeWeight V) (h s : ℝ) : demandVolume G w C A h s ≤ weightSize A := by
  classical
  exact Nat.findGreatest_le _

theorem witness_size_le_volume {G : SimpleGraph V} {w C : EdgeLength V}
    {A : NodeWeight V} {h s : ℝ} {D : Demand V} (hD : CutWitness G w C A h s D) :
    demandSize D ≤ demandVolume G w C A h s := by
  classical
  exact Nat.le_findGreatest (demandSize_le_weightSize hD.1) ⟨D, hD, rfl⟩

/-- Sparsity requires positive volume; a zero denominator is never treated
as a sparse cut merely because a totalized real division returns zero. -/
def SparseCut (G : SimpleGraph V) (U : Sym2 V → ℕ) (w : EdgeLength V)
    (A : NodeWeight V) (h s φ : ℝ) (C : EdgeLength V) : Prop :=
  (∀ e, 0 ≤ C e) ∧ 0 < demandVolume G w C A h s ∧
    cutCost G U C ≤ φ * (demandVolume G w C A h s : ℝ)

def IsExpander (G : SimpleGraph V) (U : Sym2 V → ℕ) (w : EdgeLength V)
    (A : NodeWeight V) (h s φ : ℝ) : Prop :=
  ∀ C, ¬ SparseCut G U w A h s φ C

/-- The decomposition may be zero when the graph already expands. -/
def IsDecomposition (G : SimpleGraph V) (U : Sym2 V → ℕ) (w : EdgeLength V)
    (A : NodeWeight V) (h s φ κ : ℝ) (C : EdgeLength V) : Prop :=
  (∀ e, 0 ≤ C e) ∧ cutCost G U C ≤ κ * φ * (weightSize A : ℝ) ∧
    IsExpander G U (applyCut w C (h*s)) A h s φ

theorem sparseCut_size_bound {G : SimpleGraph V} {U : Sym2 V → ℕ}
    {w C : EdgeLength V} {A : NodeWeight V} {h s φ : ℝ}
    (hφ : 0 ≤ φ) (hC : SparseCut G U w A h s φ C) :
    cutCost G U C ≤ φ * (weightSize A : ℝ) := by
  exact hC.2.2.trans (mul_le_mul_of_nonneg_left
    (by exact_mod_cast volume_le_weightSize G w C A h s) hφ)

end LengthExpander
