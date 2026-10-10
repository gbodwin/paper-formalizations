import LengthExpander.CutSequenceMatching
import Mathlib.Algebra.BigOperators.Fin

/-! Direct decomposition proof from the density of the auxiliary matching
union. Its edge count is the sum of witness volumes, so no dispersion or
union-sparsity theorem is needed to bound the cost of the unscaled sum.
The separate union theorem remains an independent obligation. -/
namespace LengthExpander
open Finset SimpleGraph
attribute [local instance] Classical.propDecidable
variable {V : Type*} [Fintype V]

noncomputable def sequenceVolume (G : SimpleGraph V) (A : NodeWeight V) (h s : ℝ) :
    EdgeLength V → List (EdgeLength V) → ℕ
  | _, [] => 0
  | w, C::Cs => demandVolume G w C A h s + sequenceVolume G A h s (applyCut w C (h*s)) Cs

theorem sequenceVolume_eq_sum (G : SimpleGraph V) (A : NodeWeight V)
    (h s : ℝ) (w : EdgeLength V) (Cs : List (EdgeLength V)) :
    sequenceVolume G A h s w Cs = ∑ i : Fin Cs.length,
      demandVolume G (sequenceWeight w (h*s) Cs i.val) Cs[i.val] A h s := by
  induction Cs generalizing w with
  | nil => simp [sequenceVolume]
  | cons C Cs ih =>
    simp only [sequenceVolume,List.length_cons,Fin.sum_univ_succ,Fin.val_zero,
      sequenceWeight_zero,List.getElem_cons_zero,Fin.val_succ,sequenceWeight_cons,
      List.getElem_cons_succ]
    rw [ih]

theorem sparseSequence_cost_le_volume {G : SimpleGraph V} {U : Sym2 V → ℕ}
    {A : NodeWeight V} {h s φ : ℝ} {w : EdgeLength V} {Cs : List (EdgeLength V)}
    (hCs : SparseSequence G U A h s φ w Cs) :
    cutCost G U (totalCut Cs) ≤ φ * (sequenceVolume G A h s w Cs : ℝ) := by
  induction Cs generalizing w with
  | nil => simp [sequenceVolume]
  | cons C Cs ih =>
    rw [totalCut_cons,cutCost_add]
    have htail := ih hCs.2
    simpa only [sequenceVolume,Nat.cast_add,mul_add] using add_le_add hCs.1.2.2 htail

/-- Edge form of the checked average-degree bound, including empty graphs. -/
theorem parallelGreedy_edge_budget {G : SimpleGraph V} {index : Sym2 V → ℕ} {s : ℕ}
    (H : IsParallelGreedy G index s) (hs : 2 ≤ s) :
    (Fintype.card G.edgeSet : ℝ) ≤
      4*(s:ℝ)*(Fintype.card V : ℝ)^(2/(s:ℝ))*(Fintype.card V : ℝ) := by
  classical
  have hcard : G.edgeFinset.card = Fintype.card G.edgeSet := by
    simp [edgeFinset,Set.toFinset_card]
  by_cases hn : Fintype.card V = 0
  · letI : IsEmpty V := Fintype.card_eq_zero_iff.mp hn
    have hG : G = ⊥ := by ext u; exact isEmptyElim u
    simp [hG,hn]
  · have hn' : (0 : ℝ) < Fintype.card V := by exact_mod_cast Nat.pos_of_ne_zero hn
    have hb := (div_le_iff₀ hn').mp (uniform_average_degree_bound H hs)
    rw [hcard] at hb
    nlinarith

/-- Direct total witness-volume bound for any finite sparse-cut sequence. -/
theorem sparseSequence_volume_bound {G : SimpleGraph V} {U : Sym2 V → ℕ}
    {A : NodeWeight V} {h φ : ℝ} {s : ℕ} {w : EdgeLength V} {Cs : List (EdgeLength V)}
    (hCs : SparseSequence G U A h (s:ℝ) φ w Cs) (hh : 0 ≤ h) (hs : 2 ≤ s) :
    (sequenceVolume G A h s w Cs : ℝ) ≤
      (8*(s:ℝ)*(2*(weightSize A : ℝ))^(2/(s:ℝ))) * (weightSize A : ℝ) := by
  classical
  obtain ⟨H,index,hH,hsize,_⟩ := sparseSequence_matching_forest hCs hh hs
  have he : sequenceVolume G A h s w Cs = Fintype.card H.edgeSet := by
    rw [sequenceVolume_eq_sum]
    exact hsize.symm
  rw [he]
  calc
    _ ≤ 4*(s:ℝ)*(Fintype.card (DirectedCopies A) : ℝ)^(2/(s:ℝ))*Fintype.card (DirectedCopies A) :=
      parallelGreedy_edge_budget hH hs
    _ = _ := by rw [card_directedCopies]; push_cast; ring

/-- Theorem 5.1, with explicit constant and the corrected unscaled output.
This proof bypasses the still-separate union-sparsity theorem: the auxiliary
graph's density directly bounds the total witness volume and hence cut cost.
It includes empty graphs, zero node budgets, and h=0 or phi=0. -/
theorem exists_direct_decomposition (G : SimpleGraph V) (U : Sym2 V → ℕ)
    (A : NodeWeight V) (w : EdgeLength V) (h φ : ℝ) (s : ℕ)
    (hh : 0 ≤ h) (hφ : 0 ≤ φ) (hs : 2 ≤ s) :
    ∃ C, IsDecomposition G U w A h s φ
      (8*(s:ℝ)*(2*(weightSize A : ℝ))^(2/(s:ℝ))) C := by
  obtain ⟨Cs,hCs,hExp,_⟩ := exists_finite_maximal_sequence G U A h s φ hh
    (by exact_mod_cast (show 1 ≤ s by omega)) w
  refine ⟨totalCut Cs,sequence_total_nonneg hCs,?_,hExp⟩
  have hc := sparseSequence_cost_le_volume hCs
  have hv := sparseSequence_volume_bound hCs hh hs
  have hm := mul_le_mul_of_nonneg_left hv hφ
  exact hc.trans (by nlinarith [hm])

end LengthExpander
